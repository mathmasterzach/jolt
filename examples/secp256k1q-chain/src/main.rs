use std::time::Instant;
use tracing::info;

pub fn main() {
    tracing_subscriber::fmt::init();

    let target_dir = "/tmp/jolt-guest-targets";
    let mut program = guest::compile_secp256k1q_chain(target_dir);

    let prover_preprocessing = guest::preprocess_prover_secp256k1q_chain(&mut program);
    let verifier_preprocessing =
        guest::verifier_preprocessing_from_prover_secp256k1q_chain(&prover_preprocessing);

    let prove_secp256k1q_chain =
        guest::build_prover_secp256k1q_chain(program, prover_preprocessing);
    let verify_secp256k1q_chain = guest::build_verifier_secp256k1q_chain(verifier_preprocessing);

    let input = [1u64; 4];
    let iters = 100;
    let native_output = guest::secp256k1q_chain(input, iters);
    let now = Instant::now();
    let (output, proof, program_io) = prove_secp256k1q_chain(input, iters);
    info!("Prover runtime: {} s", now.elapsed().as_secs_f64());
    let is_valid = verify_secp256k1q_chain(input, iters, output, program_io.panic, proof);

    assert_eq!(output, native_output, "output mismatch");
    info!("output: {:?}", output);
    info!("native_output: {:?}", native_output);
    info!("valid: {is_valid}");
}
