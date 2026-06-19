use crate::jolt_instruction;

jolt_instruction!(
    /// AES SBOX8W: Apply sbox each byte in 64-bit input
    AesSbox8W,
    circuit flags: [WriteLookupOutputToRD],
    instruction flags: [LeftOperandIsRs1Value, RightOperandIsRs2Value]
);
