use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

use ff::Field;

const STEPS: usize = 5;

struct TestCircuit<F: Field> {
    _ph: PhantomData<F>,
    values: Value<Vec<F>>,
}

#[derive(Clone, Debug)]
struct TestConfig<F: Field + Clone> {
    _ph: PhantomData<F>,
    q_enable: Selector,
    advice: Column<Advice>,
}

impl<F: Field> Circuit<F> for TestCircuit<F> {
    type Config = TestConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        TestCircuit {
            _ph: PhantomData,
            values: Value::unknown(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let q_enable = meta.complex_selector();
        let advice = meta.advice_column();

        // define a new gate:
        // next = curr + 1 if q_enable is 1
        meta.create_gate("step", |meta| {
            let curr = meta.query_advice(advice, Rotation::cur());
            let next = meta.query_advice(advice, Rotation::next());
            let q_enable = meta.query_selector(q_enable);
            vec![q_enable * (curr - next + Expression::Constant(F::ONE))]
        });

        TestConfig {
            _ph: PhantomData,
            q_enable,
            advice,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config, //
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "steps",
            |mut region| {
                // apply the "step" gate STEPS = 5 times
                for i in 0..STEPS {
                    // assign the witness value to the advice column
                    region.assign_advice(
                        || "assign advice",
                        config.advice,
                        i,
                        || self.values.as_ref().map(|values| values[i]),
                    )?;

                    // turn on the gate
                    config.q_enable.enable(&mut region, i)?;
                }

                // assign the final "next" value
                region.assign_advice(
                    || "assign advice",
                    config.advice,
                    STEPS,
                    || self.values.as_ref().map(|values| values[STEPS]),
                )?;

                Ok(())
            },
        )?;
        Ok(())
    }
}

fn main() {
    use halo2_proofs::halo2curves::bn256::Fr;
    let values_arr = Value::known((1..=STEPS+1).map(|x| Fr::from(x as u64)).collect());
    // println!("Values: {:?}", values_arr);
    let circuit = TestCircuit::<Fr> { _ph: PhantomData,  values: values_arr };
    let prover = MockProver::run(6, &circuit, vec![]).unwrap();
    prover.verify().unwrap();
}
