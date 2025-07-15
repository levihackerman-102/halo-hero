use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{
        Advice,
        Circuit,
        Column, //
        ConstraintSystem,
        Error,
        Fixed,
        Selector,
        TableColumn,
    },
    poly::Rotation,
};

use ff::{Field, PrimeField};

const BLOCK_LEN: usize = 16; // AES key length in bytes
const SBOX: [u8; 256] = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
];

struct TestCircuit<F: Field> {
    _ph: PhantomData<F>,
    pt: Value<Vec<u8>>, // plaintext
    ct: Value<Vec<u8>>, // ciphertext
    key: Value<Vec<u8>>, // key
}

#[derive(Clone, Debug)]
struct TestConfig<F: Field + Clone> {
    _ph: PhantomData<F>,
    q_encrypt: Selector,
    pt: Column<Advice>,
    pt_op: Column<Advice>,
    ct: Column<Advice>,
    key: Column<Advice>,
    sbox: TableColumn,
}

fn subbytes(input: &Vec<u8>) -> Vec<u8> {
    let mut output = vec![0u8; input.len()]; // Initialize with zeros
    for i in 0..4 {
        for j in 0..4 {
            output[4*i+j] = SBOX[input[4*i+j] as usize];
        }
    }
    output
}

impl<F: PrimeField> Circuit<F> for TestCircuit<F> {
    type Config = TestConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        TestCircuit {
            _ph: PhantomData,
            pt: Value::unknown(),
            ct: Value::unknown(),
            key: Value::unknown(),
        }
    }

    // ANCHOR: columns
    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let q_encrypt = meta.selector();
        let pt = meta.advice_column();
        let pt_op = meta.advice_column();
        let ct = meta.advice_column();
        let key = meta.advice_column();
        let sbox = meta.lookup_table_column();

        meta.create_gate("aes_round_encrypt", |meta| {
            let q_encrypt = meta.query_selector(q_encrypt);
            let pt_op = meta.query_advice(pt_op, Rotation::cur());
            let ct = meta.query_advice(ct, Rotation::cur());

            vec![q_encrypt * (pt_op - ct)]
        });

        TestConfig {
            _ph: PhantomData,
            q_encrypt,
            pt,
            pt_op,
            ct,
            key,
            sbox,
        }
    }

    // ANCHOR: assign_table
    fn synthesize(
        &self,
        config: Self::Config, //
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        
        // assign the sbox lookup table
        layouter.assign_table(
            || "sbox table",
            |mut table| {
                // fill the S-box table with values
                for i in 0..256 {
                    let output = F::from(SBOX[i] as u64); // replace with actual S-box lookup
                    table.assign_cell(
                        || "sbox entry",
                        config.sbox,
                        i,
                        || Value::known(output),
                    )?;
                }
                Ok(())
            },
        )?;
        // ANCHOR_END: assign_table

        // assign the plaintext, ciphertext, and key
        layouter.assign_region(
            || "assign inputs",
            |mut region| {
                for i in 0..BLOCK_LEN {
                    region.assign_advice(
                        || "plaintext",
                        config.pt,
                        i,
                        || {
                            self.pt.as_ref().map(|pt| {
                                F::from(pt[i] as u64)
                            })
                        }
                    )?;

                    region.assign_advice(
                        || "ciphertext",
                        config.ct,
                        i,
                        || {
                            self.ct.as_ref().map(|ct| {
                                F::from(ct[i] as u64)
                            })
                        }
                    )?;

                    region.assign_advice(
                        || "key",
                        config.key,
                        i,
                        || {
                            self.key.as_ref().map(|key| {
                                F::from(key[i] as u64)
                            })
                        }
                    )?;

                    let subbyte_result = self.pt.as_ref().map(|pt| subbytes(pt));

                    region.assign_advice(
                        || "subbytes output",
                        config.pt_op,
                        i,
                        || {
                            subbyte_result.as_ref().map(|result| {
                                F::from(result[i] as u64)
                            })
                        }
                    )?;

                    config.q_encrypt.enable(&mut region, i)?;
                }
                Ok(())
            },
        )?;

        Ok(())
    }
}

fn main() {
    use halo2_proofs::halo2curves::bn256::Fr;

    let plaintext = "Hello AES World!";
    // print!("{:?}", plaintext.as_bytes().to_vec());
    // round_key_bytes = b"\x2b\x7e\x15\x16\x28\xae\xd2\xa6\xab\xf7\x15\x88\x09\xcf\x4f\x3c"
    let round_key = vec![
        0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
        0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c
    ];
    // Encrypted bytes: eb495aedb2e6bb11a424ba787523bc79
    // let ciphertext = vec![0xEB, 0x49, 0x5A, 0xED, 0xB2, 0xE6, 0xBB, 0x11, 0xA4, 0x24, 0xBA, 0x78, 0x75, 0x23, 0xBC, 0x79];
    // encrypted_bytes = bytearray([0x52, 0x4D, 0x50, 0x50, 0xA8, 0xB7, 0x83, 0x6E, 0xED, 0xB7, 0x5B, 0xA8, 0x40, 0x50, 0x43, 0xFD])
    let ciphertext = vec![
        0x52, 0x4D, 0x50, 0x50, 0xA8, 0xB7, 0x83, 0x6E,
        0xED, 0xB7, 0x5B, 0xA8, 0x40, 0x50, 0x43, 0xFD
    ];

    let circuit = TestCircuit::<Fr> {
        _ph: PhantomData,
        pt: Value::known(plaintext.as_bytes().to_vec()), // convert string to bytes
        ct: Value::known(ciphertext), // placeholder for ciphertext
        key: Value::known(round_key), // placeholder for key
    };

    let prover = MockProver::run(9, &circuit, vec![]).unwrap();
    prover.verify().unwrap();
    println!("MockProver verification successful!");
}


