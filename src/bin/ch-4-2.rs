use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
    halo2curves::bn256::Fr,
};
use ff::Field;

struct TestCircuit<F: Field> {
    _ph: PhantomData<F>,
    secret: Value<F>,
}

impl<F: Field> TestCircuit<F> {
    /// This region occupies 3 rows.
    fn mul(
        config: &<Self as Circuit<F>>::Config,
        layouter: &mut impl Layouter<F>,
        lhs: AssignedCell<F, F>,
        rhs: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "mul",
            |mut region| {
                let v0 = lhs.value().cloned();
                let v1 = rhs.value().cloned();
                let v2 = v0
                .and_then(|v0| v1.and_then(|v1| Value::known(v0 * v1)));

                let w0 = region.assign_advice(
                    || "assign w0", //
                    config.advice,
                    0,
                    || Value::known(F::ONE),
                )?;

                let w1 = region.assign_advice(
                    || "assign w1", //
                    config.advice,
                    1,
                    || Value::known(F::ZERO),
                )?;

                let w2 = region.assign_advice(
                    || "assign w2", //
                    config.advice,
                    2,
                    || Value::known(F::ZERO),
                )?;

                // turn on the gate
                config.q_mul.enable(&mut region, 0)?;
                Ok(w2)
            },
        )
    }

    /// This region occupies 1 row.
    fn unconstrained(
        config: &<Self as Circuit<F>>::Config,
        layouter: &mut impl Layouter<F>,
        value: Value<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "free variable",
            |mut region| {
                region.assign_advice(
                    || "assign w0", //
                    config.advice,
                    0,
                    || value,
                )
            },
        )
    }


}

#[derive(Clone, Debug)]
struct TestConfig<F: Field + Clone> {
    _ph: PhantomData<F>,
    q_mul: Selector,
    advice: Column<Advice>,
}

impl<F: Field> Circuit<F> for TestCircuit<F> {
    type Config = TestConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        TestCircuit {
            _ph: PhantomData,
            secret: Value::unknown(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let q_enable = meta.complex_selector();
        let advice = meta.advice_column();

        // define a new gate:
        meta.create_gate("vertical-mul", |meta| {
            let w0 = meta.query_advice(advice, Rotation(0));
            let w1 = meta.query_advice(advice, Rotation(1));
            let w2 = meta.query_advice(advice, Rotation(2));
            let q_enable = meta.query_selector(q_enable);
            vec![q_enable * (w0 * w1 - w2)]
        });

        TestConfig {
            _ph: PhantomData,
            q_mul: q_enable,
            advice,
        }
    }

    fn synthesize(
    &self,
    config: Self::Config, //
    mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // create a new free variable
        let a = TestCircuit::<F>::unconstrained(
            &config, //
            &mut layouter,
            self.secret.clone(),
        )?;

        // do a few multiplications
        let a2 = TestCircuit::<F>::mul(
            &config, //
            &mut layouter,
            a.clone(),
            a.clone(),
        )?;
        let a3 = TestCircuit::<F>::mul(
            &config, //
            &mut layouter,
            a2.clone(),
            a.clone(),
        )?;
        let _a5 = TestCircuit::<F>::mul(
            &config, //
            &mut layouter,
            a3.clone(),
            a2.clone(),
        )?;

        Ok(())
    }
}

fn main() {
    let secret = Fr::from(3u64);
    let circuit = TestCircuit {
        _ph: PhantomData,
        secret: Value::known(secret),
    };
    let k = 4; // k is the number of rows in the circuit
    let prover = MockProver::run(k, &circuit, vec![]).expect("MockProver should run successfully");
    
    // Print the circuit layout and values
    match prover.verify() {
        Ok(()) => println!("Circuit is satisfied!"),
        Err(e) => println!("Circuit verification failed: {:?}", e),
    }
    
    // Print detailed information about the circuit
    // println!("{:#?}", prover);
}
