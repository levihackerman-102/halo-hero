use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};

use ff::{Field, PrimeField};

#[derive(Clone, Debug)]
struct Variable<F: Field> {
    mul: F,
    add: F,
    val: AssignedCell<F, F>,
}

impl<F: Field> Variable<F> {
    fn value(&self) -> Value<F> {
        self.val.value().map(|v| self.mul * v + self.add)
    }
}

impl<F: Field> std::ops::Add<F> for Variable<F> {
    type Output = Self;

    fn add(self, rhs: F) -> Self {
        Self {
            mul: self.mul,
            add: self.add + rhs,
            val: self.val,
        }
    }
}

impl<F: Field> std::ops::Mul<F> for Variable<F> {
    type Output = Self;

    fn mul(self, rhs: F) -> Self {
        Self {
            mul: self.mul * rhs,
            add: self.add * rhs,
            val: self.val,
        }
    }
}

#[derive(Clone, Debug)]
struct ArithmeticChip<F: Field> {
    _ph: PhantomData<F>,
    q_arith: Selector,
    c0: Column<Fixed>,
    c1: Column<Fixed>,
    c2: Column<Fixed>,
    cm: Column<Fixed>,
    cc: Column<Fixed>,
    w0: Column<Advice>,
    w1: Column<Advice>,
    w2: Column<Advice>,
}

impl<F: Field> ArithmeticChip<F> {
    fn configure(
        meta: &mut ConstraintSystem<F>,
        c0: Column<Fixed>,
        c1: Column<Fixed>,
        c2: Column<Fixed>,
        cm: Column<Fixed>,
        cc: Column<Fixed>,
        w0: Column<Advice>,
        w1: Column<Advice>,
        w2: Column<Advice>,
    ) -> Self {
        let q_arith = meta.selector();

        meta.create_gate("arith", |meta| {
            let q_arith = meta.query_selector(q_arith);
            let w0 = meta.query_advice(w0, Rotation::cur());
            let w1 = meta.query_advice(w1, Rotation::cur());
            let w2 = meta.query_advice(w2, Rotation::cur());

            let c0 = meta.query_fixed(c0, Rotation::cur());
            let c1 = meta.query_fixed(c1, Rotation::cur());
            let c2 = meta.query_fixed(c2, Rotation::cur());

            let cm = meta.query_fixed(cm, Rotation::cur());
            let cc = meta.query_fixed(cc, Rotation::cur());

            let expr = Expression::Constant(F::ZERO);
            let expr = expr + c0 * w0.clone();
            let expr = expr + c1 * w1.clone();
            let expr = expr + c2 * w2.clone();
            let expr = expr + cm * (w0 * w1);
            let expr = expr + cc;
            vec![q_arith * expr]
        });

        Self {
            _ph: PhantomData,
            q_arith,
            c0,
            c1,
            c2,
            cm,
            cc,
            w0,
            w1,
            w2,
        }
    }

    /// Add two variables
    fn add(
        &self,
        layouter: &mut impl Layouter<F>,
        lhs: Variable<F>,
        rhs: Variable<F>,
    ) -> Result<Variable<F>, Error> {
        layouter.assign_region(
            || "add",
            |mut region| {
                // turn on the arithmetic gate
                self.q_arith.enable(&mut region, 0)?;

                lhs.val.copy_advice(|| "lhs", &mut region, self.w0, 0)?;
                rhs.val.copy_advice(|| "rhs", &mut region, self.w1, 0)?;

                let val =
                    region.assign_advice(|| "res", self.w2, 0, || lhs.value() + rhs.value())?;

                region.assign_fixed(|| "c0", self.c0, 0, || Value::known(lhs.mul))?;
                region.assign_fixed(|| "c1", self.c1, 0, || Value::known(rhs.mul))?;
                region.assign_fixed(|| "c2", self.c2, 0, || Value::known(-F::ONE))?;
                region.assign_fixed(|| "cc", self.cc, 0, || Value::known(lhs.add + rhs.add))?;
                region.assign_fixed(|| "cm", self.cm, 0, || Value::known(F::ZERO))?;

                Ok(Variable {
                    mul: F::ONE,
                    add: F::ZERO,
                    val,
                })
            },
        )
    }

    /// Multiply two variables
    fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        lhs: Variable<F>,
        rhs: Variable<F>,
    ) -> Result<Variable<F>, Error> {
        layouter.assign_region(
            || "mul",
            |mut region| {
                // turn on the arithmetic gate
                self.q_arith.enable(&mut region, 0)?;

                // (c0 * w0 + cc1) * (c1 * w1 + cc2)
                // c0 * c1 * (w0 * w1) + c0 * cc2 * w0 + c1 * cc1 * w1 + cc1 * cc2
                lhs.val.copy_advice(|| "lhs", &mut region, self.w0, 0)?;
                rhs.val.copy_advice(|| "rhs", &mut region, self.w1, 0)?;

                let val =
                    region.assign_advice(|| "res", self.w2, 0, || lhs.value() * rhs.value())?;

                region.assign_fixed(|| "c0", self.c0, 0, || Value::known(lhs.mul * rhs.add))?;
                region.assign_fixed(|| "c1", self.c1, 0, || Value::known(rhs.mul * lhs.add))?;
                region.assign_fixed(|| "c2", self.c2, 0, || Value::known(-F::ONE))?;
                region.assign_fixed(|| "cc", self.cc, 0, || Value::known(lhs.add * rhs.add))?;
                region.assign_fixed(|| "cm", self.cm, 0, || Value::known(lhs.mul * rhs.mul))?;

                Ok(Variable {
                    mul: F::ONE,
                    add: F::ZERO,
                    val,
                })
            },
        )
    }

    fn free(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
    ) -> Result<Variable<F>, Error> {
        layouter.assign_region(
            || "free",
            |mut region| {
                // assign the value to the cell
                let cell = region.assign_advice(|| "assign free", self.w0, 0, || value)?;

                // constrain the cell to be equal to itself
                region.constrain_equal(cell.cell(), cell.cell())?;

                Ok(Variable {
                    mul: F::ONE,
                    add: F::ZERO,
                    val: cell,
                })
            },
        )
    }

    /// Assert equal
    fn eq_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: F,
        variable: Variable<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "eq_constant",
            |mut region| {
                // turn on the arithmetic gate
                self.q_arith.enable(&mut region, 0)?;

                variable
                    .val
                    .copy_advice(|| "val", &mut region, self.w0, 0)?;

                let delta = variable.add - constant;

                region.assign_advice(|| "junk1", self.w1, 0, || Value::known(F::ZERO))?;
                region.assign_advice(|| "junk2", self.w2, 0, || Value::known(F::ZERO))?;

                region.assign_fixed(|| "c0", self.c0, 0, || Value::known(variable.mul))?;
                region.assign_fixed(|| "c1", self.c1, 0, || Value::known(F::ZERO))?;
                region.assign_fixed(|| "c2", self.c2, 0, || Value::known(F::ZERO))?;
                region.assign_fixed(|| "cc", self.cc, 0, || Value::known(delta))?;
                region.assign_fixed(|| "cm", self.cm, 0, || Value::known(F::ZERO))?;

                Ok(())
            },
        )
    }

    fn eq_cells(
        &self,
        layouter: &mut impl Layouter<F>,
        lhs: Variable<F>,
        rhs: Variable<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "eq_cells",
            |mut region| {
                // enable the arithmetic gate
                self.q_arith.enable(&mut region, 0)?;

                lhs.val.copy_advice(|| "lhs", &mut region, self.w0, 0)?;
                rhs.val.copy_advice(|| "rhs", &mut region, self.w1, 0)?;

                // Set up the gate to check: c0 * w0 + c1 * w1 + cc = 0
                // Which means: w0 = -c1/c0 * w1 - cc/c0
                region.assign_fixed(|| "c0", self.c0, 0, || Value::known(F::ONE))?;
                region.assign_fixed(|| "c1", self.c1, 0, || Value::known(-F::ONE))?;
                region.assign_fixed(|| "c2", self.c2, 0, || Value::known(F::ZERO))?;
                region.assign_fixed(|| "cc", self.cc, 0, || Value::known(F::ZERO))?;
                region.assign_fixed(|| "cm", self.cm, 0, || Value::known(F::ZERO))?;

                // We don't need to assign w2 since its coefficient is zero
                region.assign_advice(|| "assign w2", self.w2, 0, || Value::known(F::ZERO))?;

                Ok(())
            },
        )
    }
}

#[derive(Clone, Debug)]
struct TestConfig<F: Field + Clone> {
    _ph: PhantomData<F>,
    arithmetic_chip: ArithmeticChip<F>,
}

#[derive(Clone, Debug)]
struct TestCircuit<F: Field> {
    _ph: PhantomData<F>,
    secret: Value<F>
}

impl<F: PrimeField> Circuit<F> for TestCircuit<F> {
    type Config = TestConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        TestCircuit {
            _ph: PhantomData,
            secret: Value::unknown(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // let q_enable = meta.fixed_column();
        let w0 = meta.advice_column();
        let w1 = meta.advice_column();
        let w2 = meta.advice_column();

        let c0 = meta.fixed_column();
        let c1 = meta.fixed_column();
        let c2 = meta.fixed_column();
        let cm = meta.fixed_column();
        let cc = meta.fixed_column();

        // enable equality constraints
        meta.enable_equality(w0);
        meta.enable_equality(w1);
        meta.enable_equality(w2);

        meta.enable_equality(cc);

        let arithmetic_chip = ArithmeticChip::configure(meta, c0, c1, c2, cm, cc, w0, w1, w2);

        TestConfig {
            _ph: PhantomData,
            arithmetic_chip,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config, //
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let a1 = config
            .arithmetic_chip
            .free(&mut layouter, self.secret.clone())?;

        let a2 = config
            .arithmetic_chip
            .add(&mut layouter, a1.clone(), a1.clone())?;

        let a3 = config
            .arithmetic_chip
            .mul(&mut layouter, a1.clone(), a2.clone())?;

        config
            .arithmetic_chip
            .eq_constant(&mut layouter, F::from_u128(1337 * (1337 + 1337)), a3)?;

        Ok(())
    }
}

fn main() {
    use halo2_proofs::halo2curves::bn256::Fr;

    // Define a test circuit with a secret value
    let circuit = TestCircuit {
        _ph: PhantomData,
        secret: Value::known(Fr::from(1337)), // Example secret value
    };

    // Create a mock prover to test the circuit
    let prover = MockProver::run(8, &circuit, vec![]).unwrap();
    prover.verify().unwrap();
    println!("Circuit verified successfully!");
}
