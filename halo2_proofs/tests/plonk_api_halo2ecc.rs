#![allow(clippy::many_single_char_names)]
#![allow(clippy::op_ref)]

use assert_matches::assert_matches;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::{AssignedCell, Cell, Chip, Layouter, Region, SimpleFloorPlanner};
use halo2_proofs::dev::MockProver;
use halo2_proofs::plonk::{
    create_proof, keygen_pk, keygen_vk, verify_proof, Advice, BatchVerifier, Circuit, Column,
    ConstraintSystem, Error, Fixed, Instance, Selector, SingleVerifier, TableColumn, VerifyingKey,
};

use halo2_proofs::poly::{
    commitment::{Params, ParamsVerifier},
    Rotation,
};
use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
use rand::SeedableRng;
use rand::prelude::StdRng;
use rand_core::OsRng;
use rand_core::block::{BlockRng, BlockRngCore};
use rand_pcg::Pcg32;
use std::marker::PhantomData;

use pairing::bn256::Fr as Fp;
use pairing::bn256::{Bn256, G1Affine};

#[test]
fn plonk_api_halo2ecc() {
    const K: u32 = 5;
    let public_inputs_size = 1;

    /// This represents an advice column at a certain row in the ConstraintSystem
    #[derive(Copy, Clone, Debug)]
    pub struct Variable(Column<Advice>, usize);

    // Initialize the polynomial commitment parameters
    let params: Params<G1Affine> = Params::<G1Affine>::unsafe_setup_rng::<Bn256, _>(K, Pcg32::seed_from_u64(42),);
    let params_verifier: ParamsVerifier<Bn256> = params.verifier(public_inputs_size).unwrap();

    #[derive(Clone, Debug)]
    struct PlonkConfig {
        /// For this chip, we will use two advice columns to implement our instructions.
        /// These are also the columns through which we communicate with other parts of
        /// the circuit.
        advice: [Column<Advice>; 2],

        /// This is the public input (instance) column.
        instance: Column<Instance>,

        // We need a selector to enable the multiplication gate, so that we aren't placing
        // any constraints on cells where `NumericInstructions::mul` is not being used.
        // This is important when building larger circuits, where columns are used by
        // multiple sets of instructions.
        s_mul: Selector,
    }

    #[derive(Clone)]
    struct MyCircuit<F: FieldExt> {
        a: Option<F>,
        b: Option<F>,
    }

    struct StandardPlonk<F: FieldExt> {
        config: PlonkConfig,
        _marker: PhantomData<F>,
    }
    struct Number<F: FieldExt>(AssignedCell<F, F>);

    trait NumericInstructions<F: FieldExt>: Chip<F> {
        /// Variable representing a number.
        type Num;

        /// Loads a number into the circuit as a private input.
        fn load_private(
            &self,
            layouter: impl Layouter<F>,
            a: Option<F>,
        ) -> Result<Self::Num, Error>;

        /// Returns `c = a * b`.
        fn mul(
            &self,
            layouter: impl Layouter<F>,
            a: Self::Num,
            b: Self::Num,
        ) -> Result<Self::Num, Error>;

        /// Exposes a number as a public input to the circuit.
        fn expose_public(
            &self,
            layouter: impl Layouter<F>,
            num: Self::Num,
            row: usize,
        ) -> Result<(), Error>;
    }

    impl<F: FieldExt> Chip<F> for StandardPlonk<F> {
        type Config = PlonkConfig;
        type Loaded = ();

        fn config(&self) -> &Self::Config {
            &self.config
        }

        fn loaded(&self) -> &Self::Loaded {
            &()
        }
    }
    impl<F: FieldExt> StandardPlonk<F> {
        fn construct(config: <Self as Chip<F>>::Config) -> Self {
            Self {
                config,
                _marker: PhantomData,
            }
        }

        fn configure(
            meta: &mut ConstraintSystem<F>,
            advice: [Column<Advice>; 2],
            instance: Column<Instance>,
        ) -> <Self as Chip<F>>::Config {
            meta.enable_equality(instance);
            for column in &advice {
                meta.enable_equality(*column);
            }
            let s_mul = meta.selector();

            // Define our multiplication gate!
            meta.create_gate("mul", |meta| {
                // To implement multiplication, we need three advice cells and a selector
                // cell. We arrange them like so:
                //
                // | a0  | a1  | s_mul |
                // |-----|-----|-------|
                // | lhs | rhs | s_mul |
                // | out |     |       |
                //
                // Gates may refer to any relative offsets we want, but each distinct
                // offset adds a cost to the proof. The most common offsets are 0 (the
                // current row), 1 (the next row), and -1 (the previous row), for which
                // `Rotation` has specific constructors.
                let lhs = meta.query_advice(advice[0], Rotation::cur());
                let rhs = meta.query_advice(advice[1], Rotation::cur());
                let out = meta.query_advice(advice[0], Rotation::next());
                let s_mul = meta.query_selector(s_mul);

                // Finally, we return the polynomial expressions that constrain this gate.
                // For our multiplication gate, we only need a single polynomial constraint.
                //
                // The polynomial expressions returned from `create_gate` will be
                // constrained by the proving system to equal zero. Our expression
                // has the following properties:
                // - When s_mul = 0, any value is allowed in lhs, rhs, and out.
                // - When s_mul != 0, this constrains lhs * rhs = out.
                vec![s_mul * (lhs * rhs - out)]
            });

            PlonkConfig {
                advice,
                instance,
                s_mul,
            }
        }
    }
    impl<F: FieldExt> NumericInstructions<F> for StandardPlonk<F> {
        type Num = Number<F>;

        fn load_private(
            &self,
            mut layouter: impl Layouter<F>,
            value: Option<F>,
        ) -> Result<Self::Num, Error> {
            let config = self.config();

            layouter.assign_region(
                || "load private",
                |mut region| {
                    region
                        .assign_advice(
                            || "private input",
                            config.advice[0],
                            0,
                            || value.ok_or(Error::Synthesis),
                        )
                        .map(Number)
                },
            )
        }

        fn mul(
            &self,
            mut layouter: impl Layouter<F>,
            a: Self::Num,
            b: Self::Num,
        ) -> Result<Self::Num, Error> {
            let config = self.config();

            layouter.assign_region(
                || "mul",
                |mut region: Region<'_, F>| {
                    // We only want to use a single multiplication gate in this region,
                    // so we enable it at region offset 0; this means it will constrain
                    // cells at offsets 0 and 1.
                    config.s_mul.enable(&mut region, 0)?;

                    // The inputs we've been given could be located anywhere in the circuit,
                    // but we can only rely on relative offsets inside this region. So we
                    // assign new cells inside the region and constrain them to have the
                    // same values as the inputs.
                    a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                    b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

                    // Now we can assign the multiplication result, which is to be assigned
                    // into the output position.
                    let value = a.0.value().and_then(|a| b.0.value().map(|b| *a * *b));

                    // Finally, we do the assignment to the output, returning a
                    // variable to be used in another part of the circuit.
                    region
                        .assign_advice(
                            || "lhs * rhs",
                            config.advice[0],
                            1,
                            || value.ok_or(Error::Synthesis),
                        )
                        .map(Number)
                },
            )
        }

        fn expose_public(
            &self,
            mut layouter: impl Layouter<F>,
            num: Self::Num,
            row: usize,
        ) -> Result<(), Error> {
            let config = self.config();

            layouter.constrain_instance(num.0.cell(), config.instance, row)
        }
    }

    impl<FF: FieldExt> StandardPlonk<FF> {
        fn new(config: PlonkConfig) -> Self {
            StandardPlonk {
                config,
                _marker: PhantomData,
            }
        }
    }

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = PlonkConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self { a: None, b: None }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> PlonkConfig {
            let advice = [meta.advice_column(), meta.advice_column()];

            let instance = meta.instance_column();

            StandardPlonk::configure(meta, advice, instance)
        }

        fn synthesize(
            &self,
            config: PlonkConfig,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let field_chip = StandardPlonk::<F>::construct(config);

            let a = field_chip.load_private(layouter.namespace(|| "load a"), self.a)?;
            let b = field_chip.load_private(layouter.namespace(|| "load a"), self.b)?;

            let c = field_chip.mul(layouter.namespace(|| "a*b"), a, b)?;

            field_chip.expose_public(layouter.namespace(|| "expose c"), c, 0)
        }
    }

    let a = Fp::from(1);
    let b = Fp::from(1);
    let instance = Fp::one();

    let empty_circuit: MyCircuit<Fp> = MyCircuit { a: None, b: None };

    let circuit: MyCircuit<Fp> = MyCircuit {
        a: Some(a),
        b: Some(b),
    };
    /*
        // Check that we get an error if we try to initialize the proving key with a value of
        // k that is too small for the minimum required number of rows.
        let much_too_small_params: Params<G1Affine> = Params::<G1Affine>::unsafe_setup::<Bn256>(1);
        assert_matches!(
            keygen_vk(&much_too_small_params, &empty_circuit),
            Err(Error::NotEnoughRowsAvailable {
                current_k,
            }) if current_k == 1
        );
    */
    // Check that we get an error if we try to initialize the proving key with a value of
    // k that is too small for the number of rows the circuit uses.
    /*
        let slightly_too_small_params: Params<G1Affine> =
            Params::<G1Affine>::unsafe_setup::<Bn256>(K - 1);
        assert_matches!(
            keygen_vk(&slightly_too_small_params, &empty_circuit),
            Err(Error::NotEnoughRowsAvailable {
                current_k,
            }) if current_k == K - 1
        );
    */
    // Initialize the proving key
    let vk = keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should not fail");

    let pubinputs = vec![instance];

    // Check this circuit is satisfied.
    let prover = match MockProver::run(K, &circuit, vec![pubinputs.clone()]) {
        Ok(prover) => prover,
        Err(e) => panic!("{:?}", e),
    };
    assert_eq!(prover.verify(), Ok(()));

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    // Create a proof
    create_proof(
        &params,
        &pk,
        &[circuit.clone()],
        &[&[&[instance]]],
        Pcg32::seed_from_u64(42),
        &mut transcript,
    )
    .expect("proof generation should not fail");
    let proof: Vec<u8> = transcript.finalize();

    // Test single-verifier strategy.
    let strategy = SingleVerifier::new(&params_verifier);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    assert!(verify_proof(
        &params_verifier,
        pk.get_vk(),
        strategy,
        &[&[&[instance]]],
        &mut transcript,
    )
    .is_ok());
}
