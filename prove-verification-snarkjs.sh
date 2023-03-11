### Prove
node example_js/generate_witness.js example_js/example.wasm ./inputs.json ./witness.wtns
snarkjs groth16 prove example_circuit_final.zkey witness.wtns proof.json public.json
snarkjs groth16 verify verification_key.json public.json proof.json



### Verification
snarkjs groth16 verify verification_key.json public.json proof.json
