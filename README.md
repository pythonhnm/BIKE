# BIKE
NIST Post-Quantum KEM BIKE (Bit Flipping Key Encapsulation) in pure Python (Python3.10.5).
Based on 2024-10-10 version of the specification.
I don't know if the algorithm (especially the decoder part) is correct, although they passed the KAT test.
The current implementation speed is also very slow
So I do not recommend using this code in a production environment.

# Reference
The algorithm is based on https://bikesuite.org/files/v5.2/BIKE_Spec.2024.10.10.1.pdf
The code style and algorithms (such as polynomials represented by integers) are derived from https://github.com/mjosaarinen/hqc-py
The T-Boxes implementation of AES is referenced from https://github.com/monero-ecosystem/slow-hash
AES256_CTR_DRBG is copied from https://github.com/GiacomoPope/kyber-py
Shake XOF is copied from https://github.com/GiacomoPope/dilithium-py
