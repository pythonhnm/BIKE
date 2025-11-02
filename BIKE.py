# bike.py
# 2025-10-31 Snack H. <minshychanqaq@cock.li>
# Implementation of BIKE (Bit Flipping Key Encapsulation) based on 2024-10-10 version of the specification.
# This version combines the advantages of two polynomial representations (integers and bit lists).
# And incremental update method was added to the pre-computation in the decoding function.
# Luckily, it works. Now the speed of Level 1 can reach 3 seconds per decaps (CPython).

import os
from hashlib import shake_256, sha3_384

class Shake:
    def __init__(self, algorithm, block_length):
        self.algorithm = algorithm
        self.block_length = block_length
        self.buf = b""
        self.len_buf = 0

    def absorb(self, input_bytes):
        """
        Initialise the XOF with the seed and reset other init.
        """
        # Initalize the buffer
        self.index = 0

        # Set the reading method from hashlib digest
        self.xof_read = self.algorithm(input_bytes).digest

        # Start by requesting 5 blocks from the XOF
        self.buf = self.xof_read(5 * self.block_length)
        self.len_buf = 5 * self.block_length

    def read(self, n):
        """
        Read n bytes from the XOF
        """
        # Make sure there are enough bytes to read
        while self.index + n > self.len_buf:
            # double the size of the buffer
            self.len_buf *= 2
            self.buf = self.xof_read(self.len_buf)

        # Read from the buffer data the bytes requested
        send = self.buf[self.index : self.index + n]

        # Shift the index along the buffer
        self.index += n

        return send

    def __call__(self, input_bytes):
        self.absorb(input_bytes)
        return self

# For AES256_CTR_DRBG used in KATs Vector test, T-Boxes implementation
def aesround(b, with_mc=True): 
    def col(c1, c2, c3, c4):
        if with_mc:
            t = S1[c1] ^ S2[c2] ^ S3[c3] ^ S4[c4]
            t1 = t >> 0 & 255
            t2 = t >> 8 & 255
            t3 = t >> 16 & 255
            t4 = t >> 24 & 255
            return (
             t1, t2, t3, t4)
        else:
            return SBox[c1], SBox[c2], SBox[c3], SBox[c4]
    return col(b[0], b[5], b[10], b[15]) + col(b[4], b[9], b[14], b[3]) + col(b[8], b[13], b[2], b[7]) + col(b[12], b[1], b[6], b[11])

def kexp(k):
    cs = offset = len(k)
    target = 4 * offset + 112
    xk = [0] * target
    xk[:offset] = k[:offset]
    ct = rc = 1
    while cs < target:
        t = xk[cs - 4:cs]
        if cs % offset == 0:
            t = [
             SBox[t[1]] ^ rc, SBox[t[2]], SBox[t[3]], SBox[t[0]]]
            ct += 1
            rc = rcon[ct]
        elif len(k) == 32:
            if cs % offset == 16:
                t = [
                 SBox[t[0]], SBox[t[1]], SBox[t[2]], SBox[t[3]]]
        xk[cs:(cs + 4)] = [
         xk[cs - offset + 0] ^ t[0],
         xk[cs - offset + 1] ^ t[1],
         xk[cs - offset + 2] ^ t[2],
         xk[cs - offset + 3] ^ t[3]]
        cs += 4

    return xk

def aes(ip, k):
    ks = kexp(k)
    ip = xor_bytes(ip,ks[:16])
    for i in range(16,len(ks)-16,16):
        ip = xor_bytes(aesround(ip),ks[i:i+16])
    return xor_bytes(aesround(ip,False),ks[-16:])

class AES256_CTR_DRBG:
    def __init__(
        self, seed=None, personalization=b""
    ):
        """
        DRBG implementation based on AES-256 CTR following the document NIST SP
        800-90A Section 10.2.1

        https://csrc.nist.gov/pubs/sp/800/90/a/r1/final

        Used for deterministic randomness, particularly used for comparing the
        output of Kyber/ML-KEM against known answer tests.

        :param bytes seed: 48 byte seed, if none is supplied a seed is generated
            using ``os.urandom(48)``.
        :param bytes personalization: optional bytes, of length at most 48 used
            during instantiation of the DRBG
        """
        self.seed_length = 48
        self.reseed_interval = 2**48
        self.key = bytes([0]) * 32
        self.V = bytes([0]) * 16
        self.entropy_input = self.__check_entropy_input(seed)

        seed_material = self.__instantiate(personalization=personalization)
        self.__ctr_drbg_update(seed_material)
        self.reseed_ctr = 1

    def __check_entropy_input(self, entropy_input: bytes) -> bytes:
        """
        If no entropy given, us os.urandom, else
        check that the input is of the right length.
        """
        if entropy_input is None:
            return os.urandom(self.seed_length)
        elif len(entropy_input) != self.seed_length:
            raise ValueError(
                f"The entropy input must be of length: {self.seed_length}. "
                f"Input has length {len(entropy_input)}"
            )
        return entropy_input

    def __instantiate(self, personalization: bytes = b"") -> bytes:
        """
        Combine the input seed and optional personalisation
        string into the seed material for the DRBG

        Section 10.2.1.3.1, Page 52 (CTR_DRBG_Instantiate_algorithm)
        """
        if len(personalization) > self.seed_length:
            raise ValueError(
                f"The Personalization String must be at most length: "
                f"{self.seed_length}. Input has length {len(personalization)}"
            )
        # Ensure personalization has exactly seed_length bytes
        personalization += bytes([0]) * (
            self.seed_length - len(personalization)
        )
        # debugging
        assert len(personalization) == self.seed_length
        return xor_bytes(self.entropy_input, personalization)

    def __increment_counter(self) -> None:
        """
        Increment the internal counter of the DRBG
        """
        int_V = int.from_bytes(self.V, "big")
        new_V = (int_V + 1) % 2**128
        self.V = new_V.to_bytes(16, byteorder="big")

    def __ctr_drbg_update(self, provided_data: bytes) -> None:
        """
        Updates the internal state of the CTR_DRBG using the
        provided_data

        Section 10.2.1.2, Page 51 (CTR_DRBG_Update)
        """
        tmp = b""

        # Collect bytes from AES ECB
        while len(tmp) != self.seed_length:
            self.__increment_counter()
            tmp += aes(self.V,self.key)

        # Take the first 48 bytes
        tmp = tmp[: self.seed_length]
        tmp = xor_bytes(tmp, provided_data)

        # Set the new values of key and V
        self.key = tmp[:32]
        self.V = tmp[32:]

    def random_bytes(
        self, num_bytes: int, additional = None
    ) -> bytes:
        """
        Generate pseudorandom bytes without a generating function

        Section 10.2.1.5.1, Page 56 (CTR_DRBG_Generate_algorithm)

        :param int num_bytes: the number of random bytes requested
        :param bytes additional: optional bytes to be mixed into the generation
        :return: pseudorandom bytes extracted from the DRBG of length ``num_bytes``.
        :rtype: bytes
        """
        # We don't cover this in coverage as we would need to run the counter 2^48 times
        if self.reseed_ctr >= self.reseed_interval:  # pragma: no cover
            raise Warning("The DRBG has been exhausted! Reseed!")

        # Set the optional additional information
        if additional is None:
            additional = bytes([0]) * self.seed_length
        else:
            if len(additional) > self.seed_length:
                raise ValueError(
                    f"The additional input must be of length at most: "
                    f"{self.seed_length}. Input has length {len(additional)}"
                )
            additional += bytes([0]) * (self.seed_length - len(additional))
            self.__ctr_drbg_update(additional)

        # Collect bytes!
        tmp = b""
        while len(tmp) < num_bytes:
            self.__increment_counter()
            tmp += aes(self.V,self.key)

        # Collect only the requested number of bits
        output_bytes = tmp[:num_bytes]
        self.__ctr_drbg_update(additional)
        self.reseed_ctr += 1
        return output_bytes

def xor_bytes(a, b):
    """
    XOR two byte arrays, assume that they are
    of the same length
    """
    return bytes(a ^ b for a, b in zip(a, b))

class BIKE:
    """BIKE Key Encapsulation Mechanism"""
    
    def __init__(self, level, seed=None):
        """
        Initialize BIKE with specified security level
        
        Args:
            level: Security level (1, 3, or 5)
        """
        self.level = level
        
        # Set parameters based on security level
        if level == 1:
            self.r = 12323      # Block size
            self.w = 142        # Row weight  
            self.t = 134        # Error weight
            self.dfr_target = 2**-128  # Target DFR
        elif level == 3:
            self.r = 24659
            self.w = 206
            self.t = 199
            self.dfr_target = 2**-192
        elif level == 5:
            self.r = 40973
            self.w = 274
            self.t = 264
            self.dfr_target = 2**-256
        else:
            raise ValueError("Security level must be 1, 3, or 5")
        
        # Derived parameters
        self.n = 2 * self.r      # Code length
        self.d = self.w // 2     # Weight for h0, h1
        self.l = 256             # Shared secret size in bits
        self.r_bytes = (self.r + 7) // 8
        self.n_bytes = (self.n + 7) // 8
        self.l_bytes = self.l // 8

        # Decoder parameters (from Table 4)
        self.nb_iter = 7
        if level == 1:
            self.delta = 3
            self.threshold_a = 0.006254868353074983
            self.threshold_b = 11.101432337243956
        elif level == 3:
            self.delta = 5
            self.threshold_a = 0.004533882596007288
            self.threshold_b = 13.282669604666431
        else:  # level 5
            self.delta = 6
            self.threshold_a = 0.0036083738659016262
            self.threshold_b = 15.430866686308178

        if seed:
            self.rng = AES256_CTR_DRBG(seed).random_bytes
        else:
            self.rng = os.urandom

    def _get_rand_mod_len(self, prng, length, uniform):
        """
        Get a random position.
        """
        if uniform: # For key generation
            # Rejection Sampling
            while True:
                rand_val = int.from_bytes(prng(4), 'little')
                if rand_val - (rand_val % length) <= 0xFFFFFFFF - length:
                    return rand_val % length
        else: # For error generation
            rand_val = int.from_bytes(prng(4), 'little')
            # alternative with Lemire's trick, needs a check
            temp = (rand_val * length) & 0xFFFFFFFFFFFFFFFF
            return temp >> 32

    def _generate_sparse_rep_keccak(self, prng, weight, length, uniform=False):
        """
        Sample a constant weight word using Fisher-Yates algorithm
        """
        positions = []
        
        # Fisher-Yates
        for i in range(weight - 1, -1, -1):
            rand_pos = self._get_rand_mod_len(prng, length - i, uniform)
            rand_pos += i  # now i <= rand_pos < length
            
            # Check collision
            collision = False
            for pos in positions:
                if pos == rand_pos:
                    collision = True
                    break
            
            if collision:
                rand_pos = i
            
            positions.append(rand_pos)
        
        vector = 0
        for pos in positions:
            vector |= (1 << pos)
        
        return vector

    def _functionH(self, m, mu):
        """
        Hash function H: M × M → E_t
        
        Args:
            m: Message
            pk_prefix: First l bits of public key
        
        Returns:
            Error vector (e0, e1)
        """
        # Format seed
        seed_for_hash = m + mu
        
        # Generate e
        shake = Shake(shake_256, 136)
        shake.absorb(seed_for_hash)
        
        e = self._generate_sparse_rep_keccak(shake.read, self.t, self.n, False)
        
        # Split into e0 and e1
        e0 = e & ((1 << self.r) - 1)
        e1 = (e >> self.r) & ((1 << self.r) - 1)
        
        return e0, e1

    def _functionL(self, e):
        """
        Hash function L: R² → M
        
        Args:
            e0, e1: Error polynomials
        
        Returns:
            Hash result
        """
        # Split into e0 and e1
        e0 = e & ((1 << self.r) - 1)
        e1 = (e >> self.r) & ((1 << self.r) - 1)
        
        # Concatenate e0 and e1
        e0_bytes = e0.to_bytes(self.r_bytes, 'little')
        e1_bytes = e1.to_bytes(self.r_bytes, 'little')
        e_split = e0_bytes + e1_bytes
        
        # Use SHA3-384 and take first l bits
        hash_value = sha3_384(e_split).digest()
        return hash_value[:self.l_bytes]

    def _functionK(self, m, c0, c1):
        """
        Hash function K: M × R × M → K
        
        Args:
            m: Message
            c: Ciphertext (c0, c1)
        
        Returns:
            Shared secret K
        """
        # Concatenate m, c0, c1
        tmp1 = m + c0 + c1
        
        # Use SHA3-384 and take first l bits
        large_hash = sha3_384(tmp1).digest()
        return large_hash[:self.l_bytes]

    def _compute_syndrome(self, ct, sk):
        """
        Compute syndrome.
        """
        # syndrome: s = c0 * h0
        c0 = int.from_bytes(ct[:self.r_bytes], 'little')
        h0 = int.from_bytes(sk[:self.r_bytes], 'little')
        
        s0 = self._polynomial_multiply(c0, h0)
        return s0

    def _polynomial_multiply(self, a, b):
        """
        Multiply two polynomials in F2[x]/(x^r - 1)
        
        Args:
            a, b: Polynomials represented as integers
        
        Returns:
            Product polynomial
        """
        result = 0
        # Multiply using cyclic shift and accumulate algorithm
        for i in range(self.r):
            if (b >> i) & 1:
                result ^= ((a << i) | (a >> (self.r - i))) & ((1 << self.r) - 1)
        return result

    def _polynomial_inverse(self, a):
        """
        Compute multiplicative inverse in F2[x]/(x^r - 1) using extended Euclidean algorithm
        Based on the algorithm from BIKE specification and reference implementations
        """
        if a == 0:
            raise ValueError("Cannot invert zero polynomial")
        
        # Extended Euclidean algorithm for polynomials
        # We're working in F2[x]/(x^r - 1)
        u = a
        v = (1 << self.r) | 1  # x^r - 1 (in F2, -1 = 1)
        g1, g2 = 1, 0
        
        while u != 1:
            j = u.bit_length() - v.bit_length()
            if j < 0:
                u, v = v, u
                g1, g2 = g2, g1
                j = -j
            
            # u = u + x^j * v
            u ^= (v << j)
            # Reduce modulo x^r - 1
            if u.bit_length() > self.r:
                u ^= (1 << self.r)  # x^r ≡ 1
                u &= (1 << self.r) - 1
            
            # g1 = g1 + x^j * g2
            g1 ^= (g2 << j)
            if g1.bit_length() > self.r:
                g1 ^= (1 << self.r)
                g1 &= (1 << self.r) - 1
        
        return g1

    def _bike_flip_decoder(self, s, h0, h1):
        """
        BIKE-Flip decoder
        
        Args:
            s: Syndrome
            h0, h1: Parity check polynomials as bit lists
        
        Returns:
            Decoded error vector (e0, e1) as bit lists
        """
        # For performance
        s = bytearray((s >> i) & 1 for i in range(self.r))
        
        # Precompute the support (positions of 1s) for h0 and h1
        h0_support = [i for i in range(self.r) if (h0 >> i) & 1]
        h1_support = [i for i in range(self.r) if (h1 >> i) & 1]
        
        # Initialize error estimate
        e0 = bytearray(self.r)
        e1 = bytearray(self.r)
        
        # Calculate current syndrome: s - (e0*h0 + e1*h1)
        current_s = s[:]
        s0 = sum(s) # Hamming weight

        # Init the first group of counters
        counters_e0 = [self._calculate_counter(current_s, h0_support, pos) for pos in range(self.r)]
        counters_e1 = [self._calculate_counter(current_s, h1_support, pos) for pos in range(self.r)]

        for iteration in range(self.nb_iter):            
            current_s_weight = sum(current_s)            
            # Calculate threshold
            threshold_val = self._calculate_threshold(current_s_weight, iteration, s0)

            # Check bits in e0,e1
            for pos in range(self.r):
                if counters_e0[pos] >= threshold_val:
                    e0[pos] ^= 1
                    # Update Syndrome and Counters
                    for i in h0_support:
                        spos = (pos + i) % self.r
                        # Old value
                        old_val = current_s[spos]
                        current_s[spos] ^= 1
                        # +1 or -1
                        delta = -1 if old_val else 1
                        for k in h0_support:
                            counters_e0[spos - k] += delta
                        for k in h1_support:
                            counters_e1[spos - k] += delta
                if counters_e1[pos] >= threshold_val:
                    e1[pos] ^= 1
                    # Update Syndrome and Counters
                    for i in h1_support:
                        spos = (pos + i) % self.r
                        # Old value
                        old_val = current_s[spos]
                        current_s[spos] ^= 1
                        # +1 or -1
                        delta = -1 if old_val else 1
                        for k in h0_support:
                            counters_e0[spos - k] += delta
                        for k in h1_support:
                            counters_e1[spos - k] += delta

        # Convert to int
        return sum(bit << i for i, bit in enumerate(e0)),sum(bit << i for i, bit in enumerate(e1))

    def _calculate_counter(self, s, h_support, position):
        """
        Counter calculation using precomputed support
        
        Args:
            s: Syndrome as bit list
            h_support: Precomputed positions of 1s in h0 or h1
            position: Bit position
        
        Returns:
            Counter value
        """
        counter = 0
        for i in h_support:
            counter += s[(position + i) % self.r]
        return counter

    def _calculate_threshold(self, S, i, S0):
        """
        Calculate threshold for bit flipping
        
        Args:
            S: Current syndrome weight
            i: Iteration number
            S0: Initial syndrome weight
        
        Returns:
            Threshold value
        """
        # Affine function f_t(S0)
        f_t = self.threshold_a * S0 + self.threshold_b

        # Affine function f_t(S)
        f_tc = self.threshold_a * S + self.threshold_b # Current
        
        # Lower bounds T_i based on iteration
        if i == 0:
            T_i = f_t + self.delta
        elif i == 1:
            T_i = (2 * f_t + (self.d + 1) / 2) / 3 + self.delta
        elif i == 2:
            T_i = (f_t + 2 * (self.d + 1) / 2) / 3 + self.delta
        else:
            T_i = (self.d + 1) / 2 + self.delta
        
        return max(int(f_tc + 0.5), int(T_i + 0.5))  # Round to nearest integer

    def _get_public_key_prefix(self, h):
        """Get first l bits of public key"""
        h_bytes = h.to_bytes(self.r_bytes, 'little')
        return h_bytes[:self.l_bytes]

    def keygen(self):
        """
        BIKE Key Generation
        
        Returns:
            Private key: (h0, h1, mu, sigma)
            Public key: h
        """
        # Sample private key (h0, h1) with weight d each
        seeds = self.rng(64)
        s1 = seeds[:32]
        s2 = seeds[32:]

        shake = Shake(shake_256, 136)
        shake.absorb(s1)

        # Generate the private key
        h0 = self._generate_sparse_rep_keccak(shake.read, self.d, self.r, True)
        h1 = self._generate_sparse_rep_keccak(shake.read, self.d, self.r, True)

        # Compute h0^{-1}
        h0_inv = self._polynomial_inverse(h0)

        # Compute public key h = h1 * h0^{-1}
        h = self._polynomial_multiply(h1, h0_inv)

        # Compute mu = first l bits of h
        mu = self._get_public_key_prefix(h)

        # Sample random sigma
        sigma = s2

        # Non-compact serialization
        private_key = (h0.to_bytes(self.r_bytes, 'little') + 
                      h1.to_bytes(self.r_bytes, 'little') + 
                      mu + sigma)
        public_key = h.to_bytes(self.r_bytes, 'little')

        return private_key, public_key

    def encaps(self, public_key):
        """
        BIKE Encapsulation
        
        Args:
            public_key: Public key h
        
        Returns:
            Shared secret K, ciphertext (c0, c1)
        """
        # Restore pk from bytes
        h = int.from_bytes(public_key, 'little')

        # Sample random message m
        seeds = self.rng(64)
        m = seeds[:self.l_bytes]

        # Get public key prefix
        mu = self._get_public_key_prefix(h)

        # Compute error vector (e0, e1) = H(m, pk_prefix)
        e0, e1 = self._functionH(m, mu)

        # Compute c0 = e0 + e1 * h
        e1h = self._polynomial_multiply(e1, h)
        c0 = e0 ^ e1h

        # Compute c1 = m ⊕ L(e0, e1)
        e_combined = e0 | (e1 << self.r)
        L_val = self._functionL(e_combined)
        c1 = bytes(a ^ b for a, b in zip(m, L_val))

        # Compute shared secret K = K(m, c)
        c0_bytes = c0.to_bytes(self.r_bytes, 'little')
        ciphertext = c0_bytes + c1
        K = self._functionK(m, c0_bytes, c1)

        return K, ciphertext

    def decaps(self, private_key, ciphertext):
        """
        BIKE Decapsulation
        
        Args:
            private_key: (h0, h1, mu, sigma)
            ciphertext: (c0, c1)
        
        Returns:
            Shared secret K
        """
        # Restore sk and c0,c1 from bytes
        h0_bytes = private_key[:self.r_bytes]
        h1_bytes = private_key[self.r_bytes:2*self.r_bytes]
        mu = private_key[2*self.r_bytes:2*self.r_bytes+self.l_bytes]
        sigma = private_key[2*self.r_bytes+self.l_bytes:]

        h0 = int.from_bytes(h0_bytes, 'little')
        h1 = int.from_bytes(h1_bytes, 'little')

        c0_bytes = ciphertext[:self.r_bytes]
        c1 = ciphertext[self.r_bytes:]
        c0 = int.from_bytes(c0_bytes, 'little')

        # Compute c0 * h0 for decoding
        s = self._polynomial_multiply(c0, h0)

        # Decode: e' = decoder(c0 * h0, h0, h1)
        e0_prime, e1_prime = self._bike_flip_decoder(s, h0, h1)

        # Compute m' = c1 ⊕ L(e')
        e_prime_combined = e0_prime | (e1_prime << self.r)
        L_val = self._functionL(e_prime_combined)
        m_prime = bytes(a ^ b for a, b in zip(c1, L_val))

        # Verify: if e' = H(m', mu) then K = K(m', c), else K = K(sigma, c)
        e0_check, e1_check = self._functionH(m_prime, mu)
        
        if e0_prime == e0_check and e1_prime == e1_check:
            K = self._functionK(m_prime, c0_bytes, c1)
        else:
            K = self._functionK(sigma, c0_bytes, c1)

        return K

# Parameter sets
BIKE_L1 = BIKE(level=1) # NIST Category 1, 128-bit in classic
BIKE_L3 = BIKE(level=3) # NIST Category 3, 192-bit in classic
BIKE_L5 = BIKE(level=5) # NIST Category 5, 256-bit in classic

# T-Boxes Constant used in AES
# KATs is not required in normal usage. You can remove these contents if you wish.
rcon = [0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36, 0x6C, 0xD8, 0xAB]
S1 = [0xa56363c6,0x847c7cf8,0x997777ee,0x8d7b7bf6,0x0df2f2ff,0xbd6b6bd6,0xb16f6fde,0x54c5c591,0x50303060,0x03010102,0xa96767ce,0x7d2b2b56,0x19fefee7,0x62d7d7b5,0xe6abab4d,0x9a7676ec,0x45caca8f,0x9d82821f,0x40c9c989,0x877d7dfa,0x15fafaef,0xeb5959b2,0xc947478e,0x0bf0f0fb,0xecadad41,0x67d4d4b3,0xfda2a25f,0xeaafaf45,0xbf9c9c23,0xf7a4a453,0x967272e4,0x5bc0c09b,0xc2b7b775,0x1cfdfde1,0xae93933d,0x6a26264c,0x5a36366c,0x413f3f7e,0x02f7f7f5,0x4fcccc83,0x5c343468,0xf4a5a551,0x34e5e5d1,0x08f1f1f9,0x937171e2,0x73d8d8ab,0x53313162,0x3f15152a,0x0c040408,0x52c7c795,0x65232346,0x5ec3c39d,0x28181830,0xa1969637,0x0f05050a,0xb59a9a2f,0x0907070e,0x36121224,0x9b80801b,0x3de2e2df,0x26ebebcd,0x6927274e,0xcdb2b27f,0x9f7575ea,0x1b090912,0x9e83831d,0x742c2c58,0x2e1a1a34,0x2d1b1b36,0xb26e6edc,0xee5a5ab4,0xfba0a05b,0xf65252a4,0x4d3b3b76,0x61d6d6b7,0xceb3b37d,0x7b292952,0x3ee3e3dd,0x712f2f5e,0x97848413,0xf55353a6,0x68d1d1b9,0x00000000,0x2cededc1,0x60202040,0x1ffcfce3,0xc8b1b179,0xed5b5bb6,0xbe6a6ad4,0x46cbcb8d,0xd9bebe67,0x4b393972,0xde4a4a94,0xd44c4c98,0xe85858b0,0x4acfcf85,0x6bd0d0bb,0x2aefefc5,0xe5aaaa4f,0x16fbfbed,0xc5434386,0xd74d4d9a,0x55333366,0x94858511,0xcf45458a,0x10f9f9e9,0x06020204,0x817f7ffe,0xf05050a0,0x443c3c78,0xba9f9f25,0xe3a8a84b,0xf35151a2,0xfea3a35d,0xc0404080,0x8a8f8f05,0xad92923f,0xbc9d9d21,0x48383870,0x04f5f5f1,0xdfbcbc63,0xc1b6b677,0x75dadaaf,0x63212142,0x30101020,0x1affffe5,0x0ef3f3fd,0x6dd2d2bf,0x4ccdcd81,0x140c0c18,0x35131326,0x2fececc3,0xe15f5fbe,0xa2979735,0xcc444488,0x3917172e,0x57c4c493,0xf2a7a755,0x827e7efc,0x473d3d7a,0xac6464c8,0xe75d5dba,0x2b191932,0x957373e6,0xa06060c0,0x98818119,0xd14f4f9e,0x7fdcdca3,0x66222244,0x7e2a2a54,0xab90903b,0x8388880b,0xca46468c,0x29eeeec7,0xd3b8b86b,0x3c141428,0x79dedea7,0xe25e5ebc,0x1d0b0b16,0x76dbdbad,0x3be0e0db,0x56323264,0x4e3a3a74,0x1e0a0a14,0xdb494992,0x0a06060c,0x6c242448,0xe45c5cb8,0x5dc2c29f,0x6ed3d3bd,0xefacac43,0xa66262c4,0xa8919139,0xa4959531,0x37e4e4d3,0x8b7979f2,0x32e7e7d5,0x43c8c88b,0x5937376e,0xb76d6dda,0x8c8d8d01,0x64d5d5b1,0xd24e4e9c,0xe0a9a949,0xb46c6cd8,0xfa5656ac,0x07f4f4f3,0x25eaeacf,0xaf6565ca,0x8e7a7af4,0xe9aeae47,0x18080810,0xd5baba6f,0x887878f0,0x6f25254a,0x722e2e5c,0x241c1c38,0xf1a6a657,0xc7b4b473,0x51c6c697,0x23e8e8cb,0x7cdddda1,0x9c7474e8,0x211f1f3e,0xdd4b4b96,0xdcbdbd61,0x868b8b0d,0x858a8a0f,0x907070e0,0x423e3e7c,0xc4b5b571,0xaa6666cc,0xd8484890,0x05030306,0x01f6f6f7,0x120e0e1c,0xa36161c2,0x5f35356a,0xf95757ae,0xd0b9b969,0x91868617,0x58c1c199,0x271d1d3a,0xb99e9e27,0x38e1e1d9,0x13f8f8eb,0xb398982b,0x33111122,0xbb6969d2,0x70d9d9a9,0x898e8e07,0xa7949433,0xb69b9b2d,0x221e1e3c,0x92878715,0x20e9e9c9,0x49cece87,0xff5555aa,0x78282850,0x7adfdfa5,0x8f8c8c03,0xf8a1a159,0x80898909,0x170d0d1a,0xdabfbf65,0x31e6e6d7,0xc6424284,0xb86868d0,0xc3414182,0xb0999929,0x772d2d5a,0x110f0f1e,0xcbb0b07b,0xfc5454a8,0xd6bbbb6d,0x3a16162c]
S2 = [0x6363c6a5,0x7c7cf884,0x7777ee99,0x7b7bf68d,0xf2f2ff0d,0x6b6bd6bd,0x6f6fdeb1,0xc5c59154,0x30306050,0x01010203,0x6767cea9,0x2b2b567d,0xfefee719,0xd7d7b562,0xabab4de6,0x7676ec9a,0xcaca8f45,0x82821f9d,0xc9c98940,0x7d7dfa87,0xfafaef15,0x5959b2eb,0x47478ec9,0xf0f0fb0b,0xadad41ec,0xd4d4b367,0xa2a25ffd,0xafaf45ea,0x9c9c23bf,0xa4a453f7,0x7272e496,0xc0c09b5b,0xb7b775c2,0xfdfde11c,0x93933dae,0x26264c6a,0x36366c5a,0x3f3f7e41,0xf7f7f502,0xcccc834f,0x3434685c,0xa5a551f4,0xe5e5d134,0xf1f1f908,0x7171e293,0xd8d8ab73,0x31316253,0x15152a3f,0x0404080c,0xc7c79552,0x23234665,0xc3c39d5e,0x18183028,0x969637a1,0x05050a0f,0x9a9a2fb5,0x07070e09,0x12122436,0x80801b9b,0xe2e2df3d,0xebebcd26,0x27274e69,0xb2b27fcd,0x7575ea9f,0x0909121b,0x83831d9e,0x2c2c5874,0x1a1a342e,0x1b1b362d,0x6e6edcb2,0x5a5ab4ee,0xa0a05bfb,0x5252a4f6,0x3b3b764d,0xd6d6b761,0xb3b37dce,0x2929527b,0xe3e3dd3e,0x2f2f5e71,0x84841397,0x5353a6f5,0xd1d1b968,0x00000000,0xededc12c,0x20204060,0xfcfce31f,0xb1b179c8,0x5b5bb6ed,0x6a6ad4be,0xcbcb8d46,0xbebe67d9,0x3939724b,0x4a4a94de,0x4c4c98d4,0x5858b0e8,0xcfcf854a,0xd0d0bb6b,0xefefc52a,0xaaaa4fe5,0xfbfbed16,0x434386c5,0x4d4d9ad7,0x33336655,0x85851194,0x45458acf,0xf9f9e910,0x02020406,0x7f7ffe81,0x5050a0f0,0x3c3c7844,0x9f9f25ba,0xa8a84be3,0x5151a2f3,0xa3a35dfe,0x404080c0,0x8f8f058a,0x92923fad,0x9d9d21bc,0x38387048,0xf5f5f104,0xbcbc63df,0xb6b677c1,0xdadaaf75,0x21214263,0x10102030,0xffffe51a,0xf3f3fd0e,0xd2d2bf6d,0xcdcd814c,0x0c0c1814,0x13132635,0xececc32f,0x5f5fbee1,0x979735a2,0x444488cc,0x17172e39,0xc4c49357,0xa7a755f2,0x7e7efc82,0x3d3d7a47,0x6464c8ac,0x5d5dbae7,0x1919322b,0x7373e695,0x6060c0a0,0x81811998,0x4f4f9ed1,0xdcdca37f,0x22224466,0x2a2a547e,0x90903bab,0x88880b83,0x46468cca,0xeeeec729,0xb8b86bd3,0x1414283c,0xdedea779,0x5e5ebce2,0x0b0b161d,0xdbdbad76,0xe0e0db3b,0x32326456,0x3a3a744e,0x0a0a141e,0x494992db,0x06060c0a,0x2424486c,0x5c5cb8e4,0xc2c29f5d,0xd3d3bd6e,0xacac43ef,0x6262c4a6,0x919139a8,0x959531a4,0xe4e4d337,0x7979f28b,0xe7e7d532,0xc8c88b43,0x37376e59,0x6d6ddab7,0x8d8d018c,0xd5d5b164,0x4e4e9cd2,0xa9a949e0,0x6c6cd8b4,0x5656acfa,0xf4f4f307,0xeaeacf25,0x6565caaf,0x7a7af48e,0xaeae47e9,0x08081018,0xbaba6fd5,0x7878f088,0x25254a6f,0x2e2e5c72,0x1c1c3824,0xa6a657f1,0xb4b473c7,0xc6c69751,0xe8e8cb23,0xdddda17c,0x7474e89c,0x1f1f3e21,0x4b4b96dd,0xbdbd61dc,0x8b8b0d86,0x8a8a0f85,0x7070e090,0x3e3e7c42,0xb5b571c4,0x6666ccaa,0x484890d8,0x03030605,0xf6f6f701,0x0e0e1c12,0x6161c2a3,0x35356a5f,0x5757aef9,0xb9b969d0,0x86861791,0xc1c19958,0x1d1d3a27,0x9e9e27b9,0xe1e1d938,0xf8f8eb13,0x98982bb3,0x11112233,0x6969d2bb,0xd9d9a970,0x8e8e0789,0x949433a7,0x9b9b2db6,0x1e1e3c22,0x87871592,0xe9e9c920,0xcece8749,0x5555aaff,0x28285078,0xdfdfa57a,0x8c8c038f,0xa1a159f8,0x89890980,0x0d0d1a17,0xbfbf65da,0xe6e6d731,0x424284c6,0x6868d0b8,0x414182c3,0x999929b0,0x2d2d5a77,0x0f0f1e11,0xb0b07bcb,0x5454a8fc,0xbbbb6dd6,0x16162c3a]
S3 = [0x63c6a563,0x7cf8847c,0x77ee9977,0x7bf68d7b,0xf2ff0df2,0x6bd6bd6b,0x6fdeb16f,0xc59154c5,0x30605030,0x01020301,0x67cea967,0x2b567d2b,0xfee719fe,0xd7b562d7,0xab4de6ab,0x76ec9a76,0xca8f45ca,0x821f9d82,0xc98940c9,0x7dfa877d,0xfaef15fa,0x59b2eb59,0x478ec947,0xf0fb0bf0,0xad41ecad,0xd4b367d4,0xa25ffda2,0xaf45eaaf,0x9c23bf9c,0xa453f7a4,0x72e49672,0xc09b5bc0,0xb775c2b7,0xfde11cfd,0x933dae93,0x264c6a26,0x366c5a36,0x3f7e413f,0xf7f502f7,0xcc834fcc,0x34685c34,0xa551f4a5,0xe5d134e5,0xf1f908f1,0x71e29371,0xd8ab73d8,0x31625331,0x152a3f15,0x04080c04,0xc79552c7,0x23466523,0xc39d5ec3,0x18302818,0x9637a196,0x050a0f05,0x9a2fb59a,0x070e0907,0x12243612,0x801b9b80,0xe2df3de2,0xebcd26eb,0x274e6927,0xb27fcdb2,0x75ea9f75,0x09121b09,0x831d9e83,0x2c58742c,0x1a342e1a,0x1b362d1b,0x6edcb26e,0x5ab4ee5a,0xa05bfba0,0x52a4f652,0x3b764d3b,0xd6b761d6,0xb37dceb3,0x29527b29,0xe3dd3ee3,0x2f5e712f,0x84139784,0x53a6f553,0xd1b968d1,0x00000000,0xedc12ced,0x20406020,0xfce31ffc,0xb179c8b1,0x5bb6ed5b,0x6ad4be6a,0xcb8d46cb,0xbe67d9be,0x39724b39,0x4a94de4a,0x4c98d44c,0x58b0e858,0xcf854acf,0xd0bb6bd0,0xefc52aef,0xaa4fe5aa,0xfbed16fb,0x4386c543,0x4d9ad74d,0x33665533,0x85119485,0x458acf45,0xf9e910f9,0x02040602,0x7ffe817f,0x50a0f050,0x3c78443c,0x9f25ba9f,0xa84be3a8,0x51a2f351,0xa35dfea3,0x4080c040,0x8f058a8f,0x923fad92,0x9d21bc9d,0x38704838,0xf5f104f5,0xbc63dfbc,0xb677c1b6,0xdaaf75da,0x21426321,0x10203010,0xffe51aff,0xf3fd0ef3,0xd2bf6dd2,0xcd814ccd,0x0c18140c,0x13263513,0xecc32fec,0x5fbee15f,0x9735a297,0x4488cc44,0x172e3917,0xc49357c4,0xa755f2a7,0x7efc827e,0x3d7a473d,0x64c8ac64,0x5dbae75d,0x19322b19,0x73e69573,0x60c0a060,0x81199881,0x4f9ed14f,0xdca37fdc,0x22446622,0x2a547e2a,0x903bab90,0x880b8388,0x468cca46,0xeec729ee,0xb86bd3b8,0x14283c14,0xdea779de,0x5ebce25e,0x0b161d0b,0xdbad76db,0xe0db3be0,0x32645632,0x3a744e3a,0x0a141e0a,0x4992db49,0x060c0a06,0x24486c24,0x5cb8e45c,0xc29f5dc2,0xd3bd6ed3,0xac43efac,0x62c4a662,0x9139a891,0x9531a495,0xe4d337e4,0x79f28b79,0xe7d532e7,0xc88b43c8,0x376e5937,0x6ddab76d,0x8d018c8d,0xd5b164d5,0x4e9cd24e,0xa949e0a9,0x6cd8b46c,0x56acfa56,0xf4f307f4,0xeacf25ea,0x65caaf65,0x7af48e7a,0xae47e9ae,0x08101808,0xba6fd5ba,0x78f08878,0x254a6f25,0x2e5c722e,0x1c38241c,0xa657f1a6,0xb473c7b4,0xc69751c6,0xe8cb23e8,0xdda17cdd,0x74e89c74,0x1f3e211f,0x4b96dd4b,0xbd61dcbd,0x8b0d868b,0x8a0f858a,0x70e09070,0x3e7c423e,0xb571c4b5,0x66ccaa66,0x4890d848,0x03060503,0xf6f701f6,0x0e1c120e,0x61c2a361,0x356a5f35,0x57aef957,0xb969d0b9,0x86179186,0xc19958c1,0x1d3a271d,0x9e27b99e,0xe1d938e1,0xf8eb13f8,0x982bb398,0x11223311,0x69d2bb69,0xd9a970d9,0x8e07898e,0x9433a794,0x9b2db69b,0x1e3c221e,0x87159287,0xe9c920e9,0xce8749ce,0x55aaff55,0x28507828,0xdfa57adf,0x8c038f8c,0xa159f8a1,0x89098089,0x0d1a170d,0xbf65dabf,0xe6d731e6,0x4284c642,0x68d0b868,0x4182c341,0x9929b099,0x2d5a772d,0x0f1e110f,0xb07bcbb0,0x54a8fc54,0xbb6dd6bb,0x162c3a16]
S4 = [0xc6a56363,0xf8847c7c,0xee997777,0xf68d7b7b,0xff0df2f2,0xd6bd6b6b,0xdeb16f6f,0x9154c5c5,0x60503030,0x02030101,0xcea96767,0x567d2b2b,0xe719fefe,0xb562d7d7,0x4de6abab,0xec9a7676,0x8f45caca,0x1f9d8282,0x8940c9c9,0xfa877d7d,0xef15fafa,0xb2eb5959,0x8ec94747,0xfb0bf0f0,0x41ecadad,0xb367d4d4,0x5ffda2a2,0x45eaafaf,0x23bf9c9c,0x53f7a4a4,0xe4967272,0x9b5bc0c0,0x75c2b7b7,0xe11cfdfd,0x3dae9393,0x4c6a2626,0x6c5a3636,0x7e413f3f,0xf502f7f7,0x834fcccc,0x685c3434,0x51f4a5a5,0xd134e5e5,0xf908f1f1,0xe2937171,0xab73d8d8,0x62533131,0x2a3f1515,0x080c0404,0x9552c7c7,0x46652323,0x9d5ec3c3,0x30281818,0x37a19696,0x0a0f0505,0x2fb59a9a,0x0e090707,0x24361212,0x1b9b8080,0xdf3de2e2,0xcd26ebeb,0x4e692727,0x7fcdb2b2,0xea9f7575,0x121b0909,0x1d9e8383,0x58742c2c,0x342e1a1a,0x362d1b1b,0xdcb26e6e,0xb4ee5a5a,0x5bfba0a0,0xa4f65252,0x764d3b3b,0xb761d6d6,0x7dceb3b3,0x527b2929,0xdd3ee3e3,0x5e712f2f,0x13978484,0xa6f55353,0xb968d1d1,0x00000000,0xc12ceded,0x40602020,0xe31ffcfc,0x79c8b1b1,0xb6ed5b5b,0xd4be6a6a,0x8d46cbcb,0x67d9bebe,0x724b3939,0x94de4a4a,0x98d44c4c,0xb0e85858,0x854acfcf,0xbb6bd0d0,0xc52aefef,0x4fe5aaaa,0xed16fbfb,0x86c54343,0x9ad74d4d,0x66553333,0x11948585,0x8acf4545,0xe910f9f9,0x04060202,0xfe817f7f,0xa0f05050,0x78443c3c,0x25ba9f9f,0x4be3a8a8,0xa2f35151,0x5dfea3a3,0x80c04040,0x058a8f8f,0x3fad9292,0x21bc9d9d,0x70483838,0xf104f5f5,0x63dfbcbc,0x77c1b6b6,0xaf75dada,0x42632121,0x20301010,0xe51affff,0xfd0ef3f3,0xbf6dd2d2,0x814ccdcd,0x18140c0c,0x26351313,0xc32fecec,0xbee15f5f,0x35a29797,0x88cc4444,0x2e391717,0x9357c4c4,0x55f2a7a7,0xfc827e7e,0x7a473d3d,0xc8ac6464,0xbae75d5d,0x322b1919,0xe6957373,0xc0a06060,0x19988181,0x9ed14f4f,0xa37fdcdc,0x44662222,0x547e2a2a,0x3bab9090,0x0b838888,0x8cca4646,0xc729eeee,0x6bd3b8b8,0x283c1414,0xa779dede,0xbce25e5e,0x161d0b0b,0xad76dbdb,0xdb3be0e0,0x64563232,0x744e3a3a,0x141e0a0a,0x92db4949,0x0c0a0606,0x486c2424,0xb8e45c5c,0x9f5dc2c2,0xbd6ed3d3,0x43efacac,0xc4a66262,0x39a89191,0x31a49595,0xd337e4e4,0xf28b7979,0xd532e7e7,0x8b43c8c8,0x6e593737,0xdab76d6d,0x018c8d8d,0xb164d5d5,0x9cd24e4e,0x49e0a9a9,0xd8b46c6c,0xacfa5656,0xf307f4f4,0xcf25eaea,0xcaaf6565,0xf48e7a7a,0x47e9aeae,0x10180808,0x6fd5baba,0xf0887878,0x4a6f2525,0x5c722e2e,0x38241c1c,0x57f1a6a6,0x73c7b4b4,0x9751c6c6,0xcb23e8e8,0xa17cdddd,0xe89c7474,0x3e211f1f,0x96dd4b4b,0x61dcbdbd,0x0d868b8b,0x0f858a8a,0xe0907070,0x7c423e3e,0x71c4b5b5,0xccaa6666,0x90d84848,0x06050303,0xf701f6f6,0x1c120e0e,0xc2a36161,0x6a5f3535,0xaef95757,0x69d0b9b9,0x17918686,0x9958c1c1,0x3a271d1d,0x27b99e9e,0xd938e1e1,0xeb13f8f8,0x2bb39898,0x22331111,0xd2bb6969,0xa970d9d9,0x07898e8e,0x33a79494,0x2db69b9b,0x3c221e1e,0x15928787,0xc920e9e9,0x8749cece,0xaaff5555,0x50782828,0xa57adfdf,0x038f8c8c,0x59f8a1a1,0x09808989,0x1a170d0d,0x65dabfbf,0xd731e6e6,0x84c64242,0xd0b86868,0x82c34141,0x29b09999,0x5a772d2d,0x1e110f0f,0x7bcbb0b0,0xa8fc5454,0x6dd6bbbb,0x2c3a1616]
SBox = [a&255 for a in S3]

# Print KATs
# To disable KATs, you have to remove aesround,kexp,aes,AES256_CTR_DRBG,rcon,S1~S4,SBox and the entry point below.
# In the production environment, this will be helpful to reduce file size.
# Although I still think it's best not to put these code into any actual applications.
if __name__ == "__main__":
    print('# BIKE\n')
    main_drbg = AES256_CTR_DRBG(bytes(range(48)))
    for i in range(100):
        print('count =',i)
        seed = main_drbg.random_bytes(48)
        print('seed =',seed.hex().upper())
        iut = BIKE(level=1,seed=seed)
        sk,pk = iut.keygen()
        print('pk =',pk.hex().upper())
        print('sk =',sk.hex().upper())
        sse,ct = iut.encaps(pk)
        print('ct =',ct.hex().upper())
        ssd = iut.decaps(sk,ct)
        if sse == ssd:
            print('ss =',ssd.hex().upper())
        else:
            print('Decaps failed')
            break
        print()
