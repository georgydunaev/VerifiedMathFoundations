#!/usr/bin/env python3

import os
import subprocess

def run_proof_scripts():
    """
    Run all proof scripts in the proofs directory and verify their correctness.
    """
    proofs_dir = "/botworkspace/VerifiedMathFoundations/proofs"
    if not os.path.exists(proofs_dir):
        print(f"Proofs directory not found: {proofs_dir}")
        return False

    proof_files = [f for f in os.listdir(proofs_dir) if f.endswith(".ML")]
    if not proof_files:
        print("No proof scripts found in the proofs directory.")
        return False

    all_passed = True
    for proof_file in proof_files:
        proof_path = os.path.join(proofs_dir, proof_file)
        try:
            result = subprocess.run(["ocaml", "-I", "/usr/lib/ocaml", proof_path], check=True, capture_output=True, text=True)
            print(f"Proof script {proof_file} passed.")
        except subprocess.CalledProcessError as e:
            print(f"Proof script {proof_file} failed with error: {e.stderr}")
            all_passed = False

    return all_passed

if __name__ == "__main__":
    if run_proof_scripts():
        print("All proof scripts passed.")
    else:
        print("Some proof scripts failed.")
