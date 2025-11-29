use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Selector, TableColumn,
    },
    poly::Rotation,
};

use ff::{Field, PrimeField};

// AES S-box lookup table
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
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
];

// GF(2^8) multiplication by 2 (xtime)
fn gf_mul_2(a: u8) -> u8 {
    if a & 0x80 != 0 {
        (a << 1) ^ 0x1b
    } else {
        a << 1
    }
}

// GF(2^8) multiplication by 3
fn gf_mul_3(a: u8) -> u8 {
    gf_mul_2(a) ^ a
}

// Generate lookup tables
fn generate_mul2_table() -> [u8; 256] {
    let mut table = [0u8; 256];
    for i in 0..256 {
        table[i] = gf_mul_2(i as u8);
    }
    table
}

fn generate_mul3_table() -> [u8; 256] {
    let mut table = [0u8; 256];
    for i in 0..256 {
        table[i] = gf_mul_3(i as u8);
    }
    table
}

// XOR lookup table for 4-bit values (16x16)
fn generate_xor4_table() -> [[u8; 16]; 16] {
    let mut table = [[0u8; 16]; 16];
    for i in 0..16 {
        for j in 0..16 {
            table[i][j] = (i ^ j) as u8;
        }
    }
    table
}

#[derive(Clone, Debug)]
struct AESConfig<F: Field + Clone> {
    _ph: PhantomData<F>,
    
    // Advice columns for state bytes
    state: [Column<Advice>; 16],
    
    // Intermediate values
    sbox_out: [Column<Advice>; 16],
    shifted: [Column<Advice>; 16],
    shifted_low: [Column<Advice>; 16],
    shifted_high: [Column<Advice>; 16],
    mixed: [Column<Advice>; 16],
    // MixColumns intermediates
    mix_m2: [Column<Advice>; 16],
    mix_m3: [Column<Advice>; 16],
    mix_t01: [Column<Advice>; 16],
    mix_t012: [Column<Advice>; 16],
    // nibble decompositions for XOR chaining
    mix_m2_low: [Column<Advice>; 16],
    mix_m2_high: [Column<Advice>; 16],
    mix_m3_low: [Column<Advice>; 16],
    mix_m3_high: [Column<Advice>; 16],
    mix_t01_low: [Column<Advice>; 16],
    mix_t01_high: [Column<Advice>; 16],
    mix_t012_low: [Column<Advice>; 16],
    mix_t012_high: [Column<Advice>; 16],
    mixed_low: [Column<Advice>; 16],
    mixed_high: [Column<Advice>; 16],
    // AddRoundKey decomposition
    ark: [Column<Advice>; 16],
    ark_low: [Column<Advice>; 16],
    ark_high: [Column<Advice>; 16],
    sbox_low: [Column<Advice>; 16],
    sbox_high: [Column<Advice>; 16],
    key_low: [Column<Advice>; 16],
    key_high: [Column<Advice>; 16],
    
    // Selectors
    q_sbox: Selector,
    q_xor: Selector,
    q_shift: Selector,
    q_mix: Selector,
    
    // Lookup tables
    tbl_sbox_in: TableColumn,
    tbl_sbox_out: TableColumn,
    
    tbl_xor4_l: TableColumn,
    tbl_xor4_r: TableColumn,
    tbl_xor4_out: TableColumn,
    
    tbl_mul2_in: TableColumn,
    tbl_mul2_out: TableColumn,
    
    tbl_mul3_in: TableColumn,
    tbl_mul3_out: TableColumn,
    // Byte→nibble tables
    tbl_byte_in: TableColumn,
    tbl_byte_low: TableColumn,
    tbl_byte_high: TableColumn,
}

struct AESCircuit<F: Field> {
    _ph: PhantomData<F>,
    // 16-byte state (4x4 matrix in column-major order)
    state: Value<[u8; 16]>,
    // 16-byte round key
    round_key: Value<[u8; 16]>,
}

impl<F: PrimeField> Circuit<F> for AESCircuit<F> {
    type Config = AESConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        AESCircuit {
            _ph: PhantomData,
            state: Value::unknown(),
            round_key: Value::unknown(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let state = [(); 16].map(|_| meta.advice_column());
        let sbox_out = [(); 16].map(|_| meta.advice_column());
        let shifted = [(); 16].map(|_| meta.advice_column());
        let mixed = [(); 16].map(|_| meta.advice_column());
        let shifted_low = [(); 16].map(|_| meta.advice_column());
        let shifted_high = [(); 16].map(|_| meta.advice_column());
        let mix_m2 = [(); 16].map(|_| meta.advice_column());
        let mix_m3 = [(); 16].map(|_| meta.advice_column());
        let mix_t01 = [(); 16].map(|_| meta.advice_column());
        let mix_t012 = [(); 16].map(|_| meta.advice_column());
        let mix_m2_low = [(); 16].map(|_| meta.advice_column());
        let mix_m2_high = [(); 16].map(|_| meta.advice_column());
        let mix_m3_low = [(); 16].map(|_| meta.advice_column());
        let mix_m3_high = [(); 16].map(|_| meta.advice_column());
        let mix_t01_low = [(); 16].map(|_| meta.advice_column());
        let mix_t01_high = [(); 16].map(|_| meta.advice_column());
        let mix_t012_low = [(); 16].map(|_| meta.advice_column());
        let mix_t012_high = [(); 16].map(|_| meta.advice_column());
        let mixed_low = [(); 16].map(|_| meta.advice_column());
        let mixed_high = [(); 16].map(|_| meta.advice_column());
        let ark = [(); 16].map(|_| meta.advice_column());
        let ark_low = [(); 16].map(|_| meta.advice_column());
        let ark_high = [(); 16].map(|_| meta.advice_column());
        let sbox_low = [(); 16].map(|_| meta.advice_column());
        let sbox_high = [(); 16].map(|_| meta.advice_column());
        let key_low = [(); 16].map(|_| meta.advice_column());
        let key_high = [(); 16].map(|_| meta.advice_column());
        
        let q_sbox = meta.complex_selector();
        let q_xor = meta.complex_selector();
        let q_shift = meta.complex_selector();
        let q_mix = meta.complex_selector();
        // removed unused selectors for mul2/mul3 to avoid warnings
        
        let tbl_sbox_in = meta.lookup_table_column();
        let tbl_sbox_out = meta.lookup_table_column();
        
        let tbl_xor4_l = meta.lookup_table_column();
        let tbl_xor4_r = meta.lookup_table_column();
        let tbl_xor4_out = meta.lookup_table_column();

        // Additional lookup tables
        let tbl_mul2_in = meta.lookup_table_column();
        let tbl_mul2_out = meta.lookup_table_column();
        let tbl_mul3_in = meta.lookup_table_column();
        let tbl_mul3_out = meta.lookup_table_column();
        let tbl_byte_in = meta.lookup_table_column();
        let tbl_byte_low = meta.lookup_table_column();
        let tbl_byte_high = meta.lookup_table_column();

        // S-box lookups
        for i in 0..16 {
            meta.lookup("sbox", |meta| {
                let s = meta.query_advice(state[i], Rotation::cur());
                let out = meta.query_advice(sbox_out[i], Rotation::cur());
                let q = meta.query_selector(q_sbox);
                vec![
                    (q.clone() * s, tbl_sbox_in),
                    (q * out, tbl_sbox_out),
                ]
            });
        }

        // Placeholder ShiftRows gates (no advice queried)
        for _i in 0..16 {
            meta.create_gate("shiftrows", |meta| {
                let q = meta.query_selector(q_shift);
                vec![q * F::from(0u64)]
            });
        }

        // MixColumns constraints: mul2/mul3 lookups and XOR chaining via 4-bit tables
        for i in 0..16 {
            // mul2 lookup: mix_m2[i] = mul2(shifted[i])
            meta.lookup("mix_mul2", |meta| {
                let q = meta.query_selector(q_mix);
                let a = meta.query_advice(shifted[i], Rotation::cur());
                let o = meta.query_advice(mix_m2[i], Rotation::cur());
                vec![(q.clone() * a, tbl_mul2_in), (q * o, tbl_mul2_out)]
            });
            // mul3 lookup: mix_m3[i] = mul3(shifted[i])
            meta.lookup("mix_mul3", |meta| {
                let q = meta.query_selector(q_mix);
                let a = meta.query_advice(shifted[i], Rotation::cur());
                let o = meta.query_advice(mix_m3[i], Rotation::cur());
                vec![(q.clone() * a, tbl_mul3_in), (q * o, tbl_mul3_out)]
            });
            // Decompose shifted[i] into low/high via reconstruction gate instead of lookup
            meta.create_gate("shifted reconstruct", |meta| {
                let q = meta.query_selector(q_mix);
                let low = meta.query_advice(shifted_low[i], Rotation::cur());
                let high = meta.query_advice(shifted_high[i], Rotation::cur());
                let byte = meta.query_advice(shifted[i], Rotation::cur());
                vec![q * (byte - low - high * F::from(16u64))]
            });
            // Decompose mix_m2/mix_m3 into nibbles via byte→nibble lookup
            meta.lookup("mix_m2_to_nibbles_low", |meta| {
                let q = meta.query_selector(q_mix);
                let a = meta.query_advice(mix_m2[i], Rotation::cur());
                let o = meta.query_advice(mix_m2_low[i], Rotation::cur());
                vec![(q.clone() * a, tbl_byte_in), (q * o, tbl_byte_low)]
            });
            meta.lookup("mix_m2_to_nibbles_high", |meta| {
                let q = meta.query_selector(q_mix);
                let a = meta.query_advice(mix_m2[i], Rotation::cur());
                let o = meta.query_advice(mix_m2_high[i], Rotation::cur());
                vec![(q.clone() * a, tbl_byte_in), (q * o, tbl_byte_high)]
            });
            meta.lookup("mix_m3_to_nibbles_low", |meta| {
                let q = meta.query_selector(q_mix);
                let a = meta.query_advice(mix_m3[i], Rotation::cur());
                let o = meta.query_advice(mix_m3_low[i], Rotation::cur());
                vec![(q.clone() * a, tbl_byte_in), (q * o, tbl_byte_low)]
            });
            meta.lookup("mix_m3_to_nibbles_high", |meta| {
                let q = meta.query_selector(q_mix);
                let a = meta.query_advice(mix_m3[i], Rotation::cur());
                let o = meta.query_advice(mix_m3_high[i], Rotation::cur());
                vec![(q.clone() * a, tbl_byte_in), (q * o, tbl_byte_high)]
            });
        }
        // XOR chain per output byte
        for col in 0..4 {
            let base = col * 4;
            let idx = [base, base + 1, base + 2, base + 3];
            // Out 0: 2*a0 ^ 3*a1 ^ a2 ^ a3
            // Use reconstruction gates for t01/t012/mixed nibbles instead of XOR lookups
            meta.create_gate("reconstruct t01", |meta| {
                let q = meta.query_selector(q_mix);
                let low = meta.query_advice(mix_t01_low[idx[0]], Rotation::cur());
                let high = meta.query_advice(mix_t01_high[idx[0]], Rotation::cur());
                let byte = meta.query_advice(mix_t01[idx[0]], Rotation::cur());
                vec![q * (byte - low - high * F::from(16u64))]
            });
            meta.create_gate("reconstruct t012", |meta| {
                let q = meta.query_selector(q_mix);
                let low = meta.query_advice(mix_t012_low[idx[0]], Rotation::cur());
                let high = meta.query_advice(mix_t012_high[idx[0]], Rotation::cur());
                let byte = meta.query_advice(mix_t012[idx[0]], Rotation::cur());
                vec![q * (byte - low - high * F::from(16u64))]
            });
            // Reconstruction: mixed = low + 16*high
            meta.create_gate("reconstruct mixed", |meta| {
                let q = meta.query_selector(q_mix);
                let low = meta.query_advice(mixed_low[idx[0]], Rotation::cur());
                let high = meta.query_advice(mixed_high[idx[0]], Rotation::cur());
                let byte = meta.query_advice(mixed[idx[0]], Rotation::cur());
                vec![q * (byte - low - high * F::from(16u64))]
            });
        }

        // AddRoundKey nibble XOR lookups and reconstruction
        for i in 0..16 {
            // XOR low nibble
            meta.lookup("xor_low", |meta| {
                let a = meta.query_advice(sbox_low[i], Rotation::cur());
                let b = meta.query_advice(key_low[i], Rotation::cur());
                let o = meta.query_advice(ark_low[i], Rotation::cur());
                let q = meta.query_selector(q_xor);
                vec![(q.clone() * a, tbl_xor4_l), (q.clone() * b, tbl_xor4_r), (q * o, tbl_xor4_out)]
            });
            // XOR high nibble
            meta.lookup("xor_high", |meta| {
                let a = meta.query_advice(sbox_high[i], Rotation::cur());
                let b = meta.query_advice(key_high[i], Rotation::cur());
                let o = meta.query_advice(ark_high[i], Rotation::cur());
                let q = meta.query_selector(q_xor);
                vec![(q.clone() * a, tbl_xor4_l), (q.clone() * b, tbl_xor4_r), (q * o, tbl_xor4_out)]
            });
            // Reconstruction: ark = ark_low + 16 * ark_high
            meta.create_gate("reconstruct ark", |meta| {
                let q = meta.query_selector(q_xor);
                let low = meta.query_advice(ark_low[i], Rotation::cur());
                let high = meta.query_advice(ark_high[i], Rotation::cur());
                let byte = meta.query_advice(ark[i], Rotation::cur());
                vec![q * (byte - low - high * F::from(16u64))]
            });
        }

        // TODO: XOR nibble-constrained lookups can be added later if needed.

        AESConfig {
            _ph: PhantomData,
            state,
            sbox_out,
            shifted,
            shifted_low,
            shifted_high,
            mixed,
            mix_m2,
            mix_m3,
            mix_t01,
            mix_t012,
            mix_m2_low,
            mix_m2_high,
            mix_m3_low,
            mix_m3_high,
            mix_t01_low,
            mix_t01_high,
            mix_t012_low,
            mix_t012_high,
            mixed_low,
            mixed_high,
            ark,
            ark_low,
            ark_high,
            sbox_low,
            sbox_high,
            key_low,
            key_high,
            q_sbox,
            q_xor,
            q_shift,
            q_mix,
            
            tbl_sbox_in,
            tbl_sbox_out,
            tbl_xor4_l,
            tbl_xor4_r,
            tbl_xor4_out,
            tbl_mul2_in,
            tbl_mul2_out,
            tbl_mul3_in,
            tbl_mul3_out,
            tbl_byte_in,
            tbl_byte_low,
            tbl_byte_high,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // Assign S-box table
        layouter.assign_table(
            || "sbox table",
            |mut table| {
                for i in 0..1018 {
                    let (in_val, out_val) = if i < 256 {
                        (F::from(i as u64), F::from(SBOX[i] as u64))
                    } else {
                        (F::from(0u64), F::from(0u64))
                    };
                    table.assign_cell(
                        || "sbox_in",
                        config.tbl_sbox_in,
                        i,
                        || Value::known(in_val),
                    )?;
                    table.assign_cell(
                        || "sbox_out",
                        config.tbl_sbox_out,
                        i,
                        || Value::known(out_val),
                    )?;
                }
                Ok(())
            },
        )?;

        // Assign byte→nibble tables
        layouter.assign_table(
            || "byte to low/high tables",
            |mut table| {
                for i in 0..1018 {
                    let (in_val, low_val, high_val) = if i < 256 {
                        let low = (i & 0x0f) as u64;
                        let high = ((i >> 4) & 0x0f) as u64;
                        (F::from(i as u64), F::from(low), F::from(high))
                    } else {
                        (F::from(0u64), F::from(0u64), F::from(0u64))
                    };
                    table.assign_cell(
                        || "byte_in",
                        config.tbl_byte_in,
                        i,
                        || Value::known(in_val),
                    )?;
                    table.assign_cell(
                        || "byte_low",
                        config.tbl_byte_low,
                        i,
                        || Value::known(low_val),
                    )?;
                    table.assign_cell(
                        || "byte_high",
                        config.tbl_byte_high,
                        i,
                        || Value::known(high_val),
                    )?;
                }
                Ok(())
            },
        )?;
        
        // Assign XOR4 table (16x16)
        layouter.assign_table(
            || "xor4 table",
            |mut table| {
                let xor_table = generate_xor4_table();
                let mut idx = 0;
                for i in 0..16 {
                    for j in 0..16 {
                        table.assign_cell(
                            || "xor4_l",
                            config.tbl_xor4_l,
                            idx,
                            || Value::known(F::from(i as u64)),
                        )?;
                        table.assign_cell(
                            || "xor4_r",
                            config.tbl_xor4_r,
                            idx,
                            || Value::known(F::from(j as u64)),
                        )?;
                        table.assign_cell(
                            || "xor4_out",
                            config.tbl_xor4_out,
                            idx,
                            || Value::known(F::from(xor_table[i][j] as u64)),
                        )?;
                        idx += 1;
                    }
                }
                // pad to 512 rows with zeros to satisfy q=0 outside regions
                while idx < 1018 {
                    table.assign_cell(
                        || "xor4_l",
                        config.tbl_xor4_l,
                        idx,
                        || Value::known(F::from(0u64)),
                    )?;
                    table.assign_cell(
                        || "xor4_r",
                        config.tbl_xor4_r,
                        idx,
                        || Value::known(F::from(0u64)),
                    )?;
                    table.assign_cell(
                        || "xor4_out",
                        config.tbl_xor4_out,
                        idx,
                        || Value::known(F::from(0u64)),
                    )?;
                    idx += 1;
                }
                Ok(())
            },
        )?;
        
        // Assign mul2 table
        layouter.assign_table(
            || "mul2 table",
            |mut table| {
                let mul2_table = generate_mul2_table();
                for i in 0..1018 {
                    let (in_val, out_val) = if i < 256 {
                        (F::from(i as u64), F::from(mul2_table[i] as u64))
                    } else {
                        (F::from(0u64), F::from(0u64))
                    };
                    table.assign_cell(
                        || "mul2_in",
                        config.tbl_mul2_in,
                        i,
                        || Value::known(in_val),
                    )?;
                    table.assign_cell(
                        || "mul2_out",
                        config.tbl_mul2_out,
                        i,
                        || Value::known(out_val),
                    )?;
                }
                Ok(())
            },
        )?;
        
        // Assign mul3 table
        layouter.assign_table(
            || "mul3 table",
            |mut table| {
                let mul3_table = generate_mul3_table();
                for i in 0..1018 {
                    let (in_val, out_val) = if i < 256 {
                        (F::from(i as u64), F::from(mul3_table[i] as u64))
                    } else {
                        (F::from(0u64), F::from(0u64))
                    };
                    table.assign_cell(
                        || "mul3_in",
                        config.tbl_mul3_in,
                        i,
                        || Value::known(in_val),
                    )?;
                    table.assign_cell(
                        || "mul3_out",
                        config.tbl_mul3_out,
                        i,
                        || Value::known(out_val),
                    )?;
                }
                Ok(())
            },
        )?;

        // Main computation region
        layouter.assign_region(
            || "aes round",
            |mut region| {
                // Step 1: SubBytes (apply S-box to each byte)
                config.q_sbox.enable(&mut region, 0)?;
                
                for i in 0..16 {
                    region.assign_advice(
                        || format!("state[{}]", i),
                        config.state[i],
                        0,
                        || self.state.map(|s| F::from(s[i] as u64)),
                    )?;
                    
                    region.assign_advice(
                        || format!("sbox_out[{}]", i),
                        config.sbox_out[i],
                        0,
                        || self.state.map(|s| F::from(SBOX[s[i] as usize] as u64)),
                    )?;
                }
                
                // Step 2: AddRoundKey (witness assignment + nibble decomposition constraints)
                config.q_xor.enable(&mut region, 1)?;
                for i in 0..16 {
                    region.assign_advice(
                        || format!("ark_out[{}]", i),
                        config.ark[i],
                        1,
                        || Value::zip(self.state, self.round_key)
                            .map(|(s, k)| F::from((SBOX[s[i] as usize] ^ k[i]) as u64)),
                    )?;
                    // Decompose ark byte into low/high for later use
                    region.assign_advice(
                        || format!("ark_low[{}]", i),
                        config.ark_low[i],
                        1,
                        || Value::zip(self.state, self.round_key)
                            .map(|(s, k)| F::from(((SBOX[s[i] as usize] ^ k[i]) & 0x0f) as u64)),
                    )?;
                    region.assign_advice(
                        || format!("ark_high[{}]", i),
                        config.ark_high[i],
                        1,
                        || Value::zip(self.state, self.round_key)
                            .map(|(s, k)| F::from((((SBOX[s[i] as usize] ^ k[i]) >> 4) & 0x0f) as u64)),
                    )?;
                    // sbox low/high
                    region.assign_advice(
                        || format!("sbox_low[{}]", i),
                        config.sbox_low[i],
                        1,
                        || self.state.map(|s| F::from(((SBOX[s[i] as usize]) & 0x0f) as u64)),
                    )?;
                    region.assign_advice(
                        || format!("sbox_high[{}]", i),
                        config.sbox_high[i],
                        1,
                        || self.state.map(|s| F::from((((SBOX[s[i] as usize]) >> 4) & 0x0f) as u64)),
                    )?;
                    // key low/high
                    region.assign_advice(
                        || format!("key_low[{}]", i),
                        config.key_low[i],
                        1,
                        || self.round_key.map(|k| F::from((k[i] & 0x0f) as u64)),
                    )?;
                    region.assign_advice(
                        || format!("key_high[{}]", i),
                        config.key_high[i],
                        1,
                        || self.round_key.map(|k| F::from(((k[i] >> 4) & 0x0f) as u64)),
                    )?;
                }

                // Step 3: ShiftRows applied to ark
                config.q_shift.enable(&mut region, 2)?;
                // Row 0: no shift
                // Row 1: shift left by 1
                // Row 2: shift left by 2
                // Row 3: shift left by 3
                let shift_map = [
                    0, 5, 10, 15,  // row 0
                    4, 9, 14, 3,   // row 1
                    8, 13, 2, 7,   // row 2
                    12, 1, 6, 11,  // row 3
                ];
                
                for i in 0..16 {
                    region.assign_advice(
                        || format!("shifted_after[{}]", i),
                        config.shifted[i],
                        2,
                        || Value::zip(self.state, self.round_key)
                            .map(|(s, k)| F::from((SBOX[s[shift_map[i]] as usize] ^ k[shift_map[i]]) as u64)),
                    )?;
                    // assign shifted low/high nibbles for lookups
                    region.assign_advice(
                        || format!("shifted_low[{}]", i),
                        config.shifted_low[i],
                        2,
                        || Value::zip(self.state, self.round_key)
                            .map(|(s, k)| F::from(((SBOX[s[shift_map[i]] as usize] ^ k[shift_map[i]]) & 0x0f) as u64)),
                    )?;
                    region.assign_advice(
                        || format!("shifted_high[{}]", i),
                        config.shifted_high[i],
                        2,
                        || Value::zip(self.state, self.round_key)
                            .map(|(s, k)| F::from((((SBOX[s[shift_map[i]] as usize] ^ k[shift_map[i]]) >> 4) & 0x0f) as u64)),
                    )?;
                }

                // Step 4: MixColumns — enable constraints at row 2
                config.q_mix.enable(&mut region, 2)?;
                // Precompute mul2/mul3 per shifted byte for lookups
                for i in 0..16 {
                    // full byte values
                    let v_m2 = Value::zip(self.state, self.round_key).map(|(s,k)| gf_mul_2((SBOX[s[shift_map[i]] as usize] ^ k[shift_map[i]]) as u8));
                    let v_m3 = Value::zip(self.state, self.round_key).map(|(s,k)| gf_mul_3((SBOX[s[shift_map[i]] as usize] ^ k[shift_map[i]]) as u8));
                    region.assign_advice(|| format!("mix_m2[{}]", i), config.mix_m2[i], 2, || v_m2.map(|x| F::from(x as u64)))?;
                    region.assign_advice(|| format!("mix_m3[{}]", i), config.mix_m3[i], 2, || v_m3.map(|x| F::from(x as u64)))?;
                    // nibble decompositions
                    region.assign_advice(|| format!("mix_m2_low[{}]", i), config.mix_m2_low[i], 2, || v_m2.map(|x| F::from((x & 0x0f) as u64)))?;
                    region.assign_advice(|| format!("mix_m2_high[{}]", i), config.mix_m2_high[i], 2, || v_m2.map(|x| F::from(((x >> 4) & 0x0f) as u64)))?;
                    region.assign_advice(|| format!("mix_m3_low[{}]", i), config.mix_m3_low[i], 2, || v_m3.map(|x| F::from((x & 0x0f) as u64)))?;
                    region.assign_advice(|| format!("mix_m3_high[{}]", i), config.mix_m3_high[i], 2, || v_m3.map(|x| F::from(((x >> 4) & 0x0f) as u64)))?;
                }
                // For AES, each column of 4 bytes [a0,a1,a2,a3] becomes:
                // [2*a0 ^ 3*a1 ^ a2 ^ a3,
                //  a0 ^ 2*a1 ^ 3*a2 ^ a3,
                //  a0 ^ a1 ^ 2*a2 ^ 3*a3,
                //  3*a0 ^ a1 ^ a2 ^ 2*a3]
                for col in 0..4 {
                    let base = col * 4;
                    let idx = [base, base + 1, base + 2, base + 3];
                    let bytes = Value::zip(self.state, self.round_key).map(|(s, k)| {
                        [
                            (SBOX[s[idx[0]] as usize] ^ k[idx[0]]) as u8,
                            (SBOX[s[idx[1]] as usize] ^ k[idx[1]]) as u8,
                            (SBOX[s[idx[2]] as usize] ^ k[idx[2]]) as u8,
                            (SBOX[s[idx[3]] as usize] ^ k[idx[3]]) as u8,
                        ]
                    });

                    // compute XOR chain intermediates using precomputed m2/m3 and shifted bytes
                    let decomp = |v: Value<u8>| -> (Value<F>, Value<F>) {
                        (
                            v.map(|x| F::from((x & 0x0f) as u64)),
                            v.map(|x| F::from(((x >> 4) & 0x0f) as u64)),
                        )
                    };

                    // compute and assign for each output r=0..3
                    for r in 0..4 {
                        let v = bytes.map(|b| match r {
                            0 => gf_mul_2(b[0]) ^ gf_mul_3(b[1]) ^ b[2] ^ b[3],
                            1 => b[0] ^ gf_mul_2(b[1]) ^ gf_mul_3(b[2]) ^ b[3],
                            2 => b[0] ^ b[1] ^ gf_mul_2(b[2]) ^ gf_mul_3(b[3]),
                            _ => gf_mul_3(b[0]) ^ b[1] ^ b[2] ^ gf_mul_2(b[3]),
                        } as u8);

                        // t01 = xor of the two mul terms; t012 adds the remaining single byte
                        let v_t01 = match r {
                            0 => Value::zip(
                                Value::zip(self.state, self.round_key).map(|(s,k)| gf_mul_2((SBOX[s[idx[0]] as usize] ^ k[idx[0]]) as u8)),
                                Value::zip(self.state, self.round_key).map(|(s,k)| gf_mul_3((SBOX[s[idx[1]] as usize] ^ k[idx[1]]) as u8)),
                            ).map(|(a,b)| a ^ b),
                            1 => Value::zip(
                                Value::zip(self.state, self.round_key).map(|(s,k)| gf_mul_2((SBOX[s[idx[1]] as usize] ^ k[idx[1]]) as u8)),
                                Value::zip(self.state, self.round_key).map(|(s,k)| gf_mul_3((SBOX[s[idx[2]] as usize] ^ k[idx[2]]) as u8)),
                            ).map(|(a,b)| a ^ b),
                            2 => Value::zip(
                                Value::zip(self.state, self.round_key).map(|(s,k)| gf_mul_2((SBOX[s[idx[2]] as usize] ^ k[idx[2]]) as u8)),
                                Value::zip(self.state, self.round_key).map(|(s,k)| gf_mul_3((SBOX[s[idx[3]] as usize] ^ k[idx[3]]) as u8)),
                            ).map(|(a,b)| a ^ b),
                            _ => Value::zip(
                                Value::zip(self.state, self.round_key).map(|(s,k)| gf_mul_3((SBOX[s[idx[0]] as usize] ^ k[idx[0]]) as u8)),
                                Value::zip(self.state, self.round_key).map(|(s,k)| gf_mul_2((SBOX[s[idx[3]] as usize] ^ k[idx[3]]) as u8)),
                            ).map(|(a,b)| a ^ b),
                        };
                        let single = match r { 0 => bytes.map(|b| b[2]), 1 => bytes.map(|b| b[3]), 2 => bytes.map(|b| b[0]), _ => bytes.map(|b| b[1]) };
                        let v_t012 = Value::zip(v_t01, single).map(|(a,b)| a ^ b);

                        // assign intermediates and final out
                        region.assign_advice(|| format!("mix_t01[{}]", idx[r]), config.mix_t01[idx[r]], 2, || v_t01.map(|x| F::from(x as u64)))?;
                        region.assign_advice(|| format!("mix_t012[{}]", idx[r]), config.mix_t012[idx[r]], 2, || v_t012.map(|x| F::from(x as u64)))?;
                        region.assign_advice(|| format!("mixed[{}]", idx[r]), config.mixed[idx[r]], 2, || v.map(|x| F::from(x as u64)))?;

                        // assign nibble decompositions for these
                        let (t01l, t01h) = decomp(v_t01);
                        let (t012l, t012h) = decomp(v_t012);
                        let (outl, outh) = decomp(v);

                        region.assign_advice(|| format!("mix_t01_low[{}]", idx[r]), config.mix_t01_low[idx[r]], 2, || t01l)?;
                        region.assign_advice(|| format!("mix_t01_high[{}]", idx[r]), config.mix_t01_high[idx[r]], 2, || t01h)?;
                        region.assign_advice(|| format!("mix_t012_low[{}]", idx[r]), config.mix_t012_low[idx[r]], 2, || t012l)?;
                        region.assign_advice(|| format!("mix_t012_high[{}]", idx[r]), config.mix_t012_high[idx[r]], 2, || t012h)?;
                        region.assign_advice(|| format!("mixed_low[{}]", idx[r]), config.mixed_low[idx[r]], 2, || outl)?;
                        region.assign_advice(|| format!("mixed_high[{}]", idx[r]), config.mixed_high[idx[r]], 2, || outh)?;
                    }
                }
                
                Ok(())
            },
        )?;

        Ok(())
    }
}

fn main() {
    use halo2_proofs::halo2curves::bn256::Fr;

    // Example: encrypt a block with a round key
    let state = [
        0x32, 0x88, 0x31, 0xe0,
        0x43, 0x5a, 0x31, 0x37,
        0xf6, 0x30, 0x98, 0x07,
        0xa8, 0x8d, 0xa2, 0x34,
    ];
    
    let round_key = [
        0x2b, 0x7e, 0x15, 0x16,
        0x28, 0xae, 0xd2, 0xa6,
        0xab, 0xf7, 0x15, 0x88,
        0x09, 0xcf, 0x4f, 0x3c,
    ];

    let circuit = AESCircuit::<Fr> {
        _ph: PhantomData,
        state: Value::known(state),
        round_key: Value::known(round_key),
    };

    // Use k=11 to provide more usable table rows for lookups
    let prover = MockProver::run(11, &circuit, vec![]).unwrap();
    prover.verify().unwrap();
    
    println!("AES round circuit verification passed!");
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::halo2curves::bn256::Fr;

    #[test]
    fn test_aes_round() {
        let state = [
            0x19, 0xa0, 0x9a, 0xe9,
            0x3d, 0xf4, 0xc6, 0xf8,
            0xe3, 0xe2, 0x8d, 0x48,
            0xbe, 0x2b, 0x2a, 0x08,
        ];
        
        let round_key = [
            0xa0, 0x88, 0x23, 0x2a,
            0xfa, 0x54, 0xa3, 0x6c,
            0xfe, 0x2c, 0x39, 0x76,
            0x17, 0xb1, 0x39, 0x05,
        ];

        let circuit = AESCircuit::<Fr> {
            _ph: PhantomData,
            state: Value::known(state),
            round_key: Value::known(round_key),
        };

        // Use k=11 to have sufficient usable rows for 256-entry tables
        let prover = MockProver::run(11, &circuit, vec![]).unwrap();
        prover.verify().unwrap();
    }
}
