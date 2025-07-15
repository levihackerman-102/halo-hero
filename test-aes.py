import numpy as np

class AESRound:
    """
    Implementation of a single round of AES encryption.
    This ignores the key schedule and takes the round key as input.
    """
    
    def __init__(self):
        # AES S-box for SubBytes transformation
        self.s_box = [
            0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
            0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
            0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
            0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
            0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
            0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
            0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
            0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
            0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
            0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
            0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
            0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
            0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
            0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
            0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
            0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
        ]
    
    def sub_bytes(self, state):
        """
        Apply S-box substitution to each byte in the state matrix.
        """
        result = np.zeros_like(state, dtype=np.uint8)
        for i in range(4):
            for j in range(4):
                result[i][j] = self.s_box[state[i][j]]
        return result
    
    def shift_rows(self, state):
        """
        Shift rows of the state matrix:
        - Row 0: no shift
        - Row 1: shift left by 1
        - Row 2: shift left by 2
        - Row 3: shift left by 3
        """
        result = np.zeros_like(state, dtype=np.uint8)
        for i in range(4):
            for j in range(4):
                result[i][j] = state[i][(j + i) % 4]
        return result
    
    def galois_multiply(self, a, b):
        """
        Multiply two numbers in GF(2^8) with irreducible polynomial x^8 + x^4 + x^3 + x + 1
        """
        result = 0
        for i in range(8):
            if b & 1:
                result ^= a
            high_bit = a & 0x80
            a <<= 1
            if high_bit:
                a ^= 0x1b  # x^8 + x^4 + x^3 + x + 1
            b >>= 1
        return result & 0xff
    
    def mix_columns(self, state):
        """
        Mix columns transformation using the fixed matrix:
        [2 3 1 1]
        [1 2 3 1]
        [1 1 2 3]
        [3 1 1 2]
        """
        result = np.zeros_like(state, dtype=np.uint8)
        mix_matrix = [
            [2, 3, 1, 1],
            [1, 2, 3, 1],
            [1, 1, 2, 3],
            [3, 1, 1, 2]
        ]
        
        for col in range(4):
            column = [state[row][col] for row in range(4)]
            for row in range(4):
                result[row][col] = (
                    self.galois_multiply(mix_matrix[row][0], column[0]) ^
                    self.galois_multiply(mix_matrix[row][1], column[1]) ^
                    self.galois_multiply(mix_matrix[row][2], column[2]) ^
                    self.galois_multiply(mix_matrix[row][3], column[3])
                )
        
        return result
    
    def add_round_key(self, state, round_key):
        """
        XOR the state with the round key.
        """
        return state ^ round_key
    
    def encrypt_round(self, state, round_key, is_final_round=False):
        """
        Perform one round of AES encryption.
        
        Args:
            state: 4x4 numpy array representing the current state
            round_key: 4x4 numpy array representing the round key
            is_final_round: If True, skip MixColumns (for the final round)
        
        Returns:
            4x4 numpy array representing the state after one round
        """
        # Step 1: SubBytes
        state = self.sub_bytes(state)
        
        # Step 2: ShiftRows
        state = self.shift_rows(state)
        
        # Step 3: MixColumns (skip in final round)
        if not is_final_round:
            state = self.mix_columns(state)
        
        # Step 4: AddRoundKey
        state = self.add_round_key(state, round_key)
        
        return state

def bytes_to_state(data):
    """
    Convert 16 bytes to a 4x4 state matrix (column-major order).
    """
    if len(data) != 16:
        raise ValueError("Data must be exactly 16 bytes")
    
    state = np.zeros((4, 4), dtype=np.uint8)
    for i in range(16):
        state[i % 4][i // 4] = data[i]
    return state

def state_to_bytes(state):
    """
    Convert a 4x4 state matrix back to 16 bytes (column-major order).
    """
    result = []
    for col in range(4):
        for row in range(4):
            result.append(state[row][col])
    return bytes(result)

# Example usage
if __name__ == "__main__":
    # Initialize AES round
    aes = AESRound()
    
    # Example plaintext (16 bytes)
    plaintext = b"Hello AES World!"
    print(f"Original plaintext: {plaintext}")
    print(f"Plaintext hex: {plaintext.hex()}")
    
    # Convert to state matrix
    state = bytes_to_state(plaintext)
    print(f"\nState matrix:")
    print(state)
    
    # Example round key (16 bytes) - in practice this would come from key schedule
    round_key_bytes = b"\x2b\x7e\x15\x16\x28\xae\xd2\xa6\xab\xf7\x15\x88\x09\xcf\x4f\x3c"
    round_key = bytes_to_state(round_key_bytes)
    print(f"\nRound key matrix:")
    print(round_key)
    
    # Perform one round of encryption
    encrypted_state = aes.encrypt_round(state, round_key, is_final_round=False)
    print(f"\nEncrypted state matrix:")
    print(encrypted_state)
    
    # Convert back to bytes
    encrypted_bytes = state_to_bytes(encrypted_state)
    print(f"\nEncrypted bytes: {encrypted_bytes.hex()}")
    
    # Demonstrate individual steps
    print("\n--- Step-by-step demonstration ---")
    
    # SubBytes
    after_subbytes = aes.sub_bytes(state)
    print(f"After SubBytes:")
    print(after_subbytes)
    
    # ShiftRows
    after_shiftrows = aes.shift_rows(after_subbytes)
    print(f"After ShiftRows:")
    print(after_shiftrows)
    
    # MixColumns
    after_mixcolumns = aes.mix_columns(after_shiftrows)
    print(f"After MixColumns:")
    print(after_mixcolumns)
    
    # AddRoundKey
    after_addroundkey = aes.add_round_key(after_mixcolumns, round_key)
    print(f"After AddRoundKey:")
    print(after_addroundkey)
    
    # Verify this matches our single function call
    print(f"\nVerification - states match: {np.array_equal(encrypted_state, after_addroundkey)}")
