circom circuits/example.circom --r1cs --wasm --sym
snarkjs groth16 setup example.r1cs powersOfTau28_hez_final_08.ptau example_circuit.zkey
snarkjs zkey contribute example_circuit.zkey example_circuit_001.zkey --name="Zigtur contribution" -v
snarkjs zkey contribute example_circuit_001.zkey example_circuit_002.zkey --name="Zigtur2 contribution" -v

snarkjs zkey beacon example_circuit_002.zkey example_circuit_final.zkey 7c30b29b16eb9319456cf3cf9a8966aba03428006de854dce09ef4d91006e169 10 -n="End of phase 2"

snarkjs zkey verify example.r1cs powersOfTau28_hez_final_08.ptau example_circuit_final.zkey
snarkjs zkey export verificationkey example_circuit_final.zkey verification_key.json
