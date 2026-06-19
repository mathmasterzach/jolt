use std::time::Instant;
use tracing::info;

pub fn main() {
    tracing_subscriber::fmt::init();

    let target_dir = "/tmp/jolt-guest-targets";
    let mut program = guest::compile_aes(target_dir);

    let shared_preprocessing = guest::preprocess_shared_aes(&mut program).unwrap();
    let prover_preprocessing = guest::preprocess_prover_aes(shared_preprocessing.clone());
    let verifier_setup = prover_preprocessing.generators.to_verifier_setup();
    let verifier_preprocessing =
        guest::preprocess_verifier_aes(shared_preprocessing, verifier_setup, None);

    let prove_aes = guest::build_prover_aes(program, prover_preprocessing);
    let verify_aes = guest::build_verifier_aes(verifier_preprocessing);

    let x = 0x012345679ABCDEFu64;
    //let key = [0u8; 16];

    let now = Instant::now();
    let (output, proof, program_io) = prove_aes(x);
    info!("Prover runtime: {} s", now.elapsed().as_secs_f64());
    let is_valid = verify_aes(x, output, program_io.panic, proof);

    info!("output: {:?}", output);
    info!("valid: {is_valid}");
}
