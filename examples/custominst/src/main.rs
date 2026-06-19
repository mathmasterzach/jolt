use std::time::Instant;
use tracing::info;

pub fn main() {
    tracing_subscriber::fmt::init();

    let target_dir = "/tmp/jolt-guest-targets";
    let mut program = guest::compile_custominst(target_dir);

    let shared_preprocessing = guest::preprocess_shared_custominst(&mut program).unwrap();
    let prover_preprocessing = guest::preprocess_prover_custominst(shared_preprocessing.clone());
    let verifier_setup = prover_preprocessing.generators.to_verifier_setup();
    let verifier_preprocessing =
        guest::preprocess_verifier_custominst(shared_preprocessing, verifier_setup, None);

    let prove_custominst = guest::build_prover_custominst(program, prover_preprocessing);
    let verify_custominst = guest::build_verifier_custominst(verifier_preprocessing);

    let x = 10;
    let y = 20;
    let now = Instant::now();
    let (output, proof, program_io) = prove_custominst(x, y);
    info!("Prover runtime: {} s", now.elapsed().as_secs_f64());
    let is_valid = verify_custominst(x, y, output, program_io.panic, proof);

    info!("output: {:?}", output);
    info!("valid: {is_valid}");
}
