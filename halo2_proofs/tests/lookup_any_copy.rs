use std::marker::PhantomData;

use halo2_proofs::poly::commitment::Params;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit, Column,
        ConstraintSystem, Error, Instance, Selector, SingleVerifier,
    },
    poly::{commitment::ParamsVerifier, Rotation},
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
};
use pairing::bn256::{Bn256, Fr as Fp, G1Affine};
use rand_core::SeedableRng;
use rand_pcg::Pcg32;

#[test]
fn lookup_any_dump() {
    #[derive(Clone, Debug)]
    struct MyConfig<F: FieldExt> {
        input: Column<Instance>,
        table: Column<Advice>,
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt> MyConfig<F> {
        fn configure(meta: &mut ConstraintSystem<F>) -> Self {
            let config = Self {
                input: meta.instance_column(),
                table: meta.advice_column(),
                _marker: PhantomData,
            };

            // Lookup on even numbers
            meta.lookup_any("even number", |meta| {
                let input = meta.query_instance(config.input, Rotation::cur());
                let table = meta.query_advice(config.table, Rotation::cur());

                vec![(input, table)]
            });

            config
        }

        fn load_table(&self, mut layouter: impl Layouter<F>, values: &[F]) -> Result<(), Error> {
            layouter.assign_region(
                || "load values for even lookup table",
                |mut region| {
                    for (offset, value) in values.iter().enumerate() {
                        region.assign_advice(
                            || "even table value",
                            self.table,
                            offset,
                            || Ok(*value),
                        )?;
                    }

                    Ok(())
                },
            )
        }
    }

    #[derive(Default, Clone)]
    struct MyCircuit<F: FieldExt> {
        lookup_table: Vec<F>,
    }

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = MyConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            Self::Config::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config.load_table(layouter.namespace(|| "lookup table"), &self.lookup_table)?;

            Ok(())
        }
    }

    let lookup_table = vec![
        Fp::from(0),
        Fp::from(2),
        Fp::from(4),
        Fp::from(6),
        Fp::from(8),
    ];

    let circuit = MyCircuit::<Fp> { lookup_table };

    const K: u32 = 4;
    let public_inputs_size = 2;

    let params: Params<G1Affine> =
        Params::<G1Affine>::unsafe_setup_rng::<Bn256, _>(K, Pcg32::seed_from_u64(42));

    let params_verifier: ParamsVerifier<Bn256> = params.verifier(public_inputs_size).unwrap();
    let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    let lookup = &vec![Fp::from(0), Fp::from(2)];

    create_proof(
        &params,
        &pk,
        &[circuit.clone()],
        &[&[lookup]],
        Pcg32::seed_from_u64(42),
        &mut transcript,
    )
    .expect("proof generation should not fail");

    let proof = transcript.finalize();

    // Test single-verifier strategy.
    let strategy = SingleVerifier::new(&params_verifier);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    assert!(verify_proof(
        &params_verifier,
        pk.get_vk(),
        strategy,
        &[&[lookup]],
        &mut transcript,
    )
    .is_ok());
}
