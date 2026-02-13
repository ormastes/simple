# RSA Public-Key Cryptography Utilities

Comprehensive implementation of RSA encryption, decryption, signing, and verification in Pure Simple.

**Refactored**: 2026-02-12 (1,759 lines → 10 focused modules)

## Architecture

### Core Data Structures

**`types.spl`** (464 lines)
- BigInt representation using list of limbs (base 2^30)
- Basic arithmetic: add, subtract, multiply, divide
- Bit operations: shift, get/set bit, bit length
- Comparison and normalization

**`modular.spl`** (169 lines)
- Modular exponentiation (binary method)
- Greatest Common Divisor (Euclidean algorithm)
- Extended GCD for computing modular inverse
- Least Common Multiple
- Jacobi symbol

### Random Number Generation

**`random.spl`** (62 lines)
- Linear Congruential Generator (LCG) PRNG
- Random BigInt generation with specified bit length
- Random BigInt in range [min, max)
- Seeding support

### Prime Numbers

**`primality.spl`** (224 lines)
- Miller-Rabin primality test (configurable rounds)
- Trial division with small primes (first 98 primes)
- Fermat primality test
- Random prime generation (with fallback)
- Next prime after given number
- Safe prime generation (p where (p-1)/2 is also prime)

### Key Management

**`key_gen.spl`** (114 lines)
- RSA keypair generation (default e=65537)
- Custom public exponent support
- CRT parameter computation (dP, dQ, qInv)
- Key validation and security checking (≥2048 bits)
- Modulus extraction and bit length queries
- Test keypair generation from specific primes

**Key Structures:**
- Public Key: `[n, e, bits]`
- Private Key: `[n, d, p, q, dP, dQ, qInv, bits]`

### Data Conversion

**`byte_conversion.spl`** (200 lines)
- BigInt ↔ byte array (0-255 values)
- Bytes ↔ hex string
- Text ↔ bytes (simplified UTF-8-like)
- BigInt ↔ decimal string
- Big-endian encoding for cryptographic compatibility

### Padding Schemes

**`padding.spl`** (123 lines)
- PKCS#1 v1.5 Type 2 (encryption): `00 || 02 || PS || 00 || M`
- PKCS#1 v1.5 Type 1 (signing): `00 || 01 || FF...FF || 00 || H`
- Padding removal with validation
- Simple hash function (SHA-256-like, 32 bytes)

### Encryption Operations

**`encrypt.spl`** (136 lines)
- Raw RSA encryption: `c = m^e mod n`
- Raw RSA decryption: `m = c^d mod n`
- CRT-optimized decryption (4x faster)
- Padded text encryption/decryption (PKCS#1 v1.5)
- Direct byte array encryption/decryption

### Signing Operations

**`sign.spl`** (117 lines)
- Digital signature generation (PKCS#1 v1.5)
- Signature verification
- Text and byte array signing
- Hash-then-sign pattern

### Utilities

**`utilities.spl`** (126 lines)
- PEM-like key encoding/decoding
- Public key component import/export
- Performance estimation (ops/sec)
- Maximum message size calculation

## RSA Algorithm Overview

### Key Generation
1. Choose two large primes `p` and `q` (1024+ bits each for 2048-bit key)
2. Compute `n = p × q` (modulus)
3. Compute `φ(n) = (p-1)(q-1)` (Euler's totient)
4. Choose `e` (public exponent, commonly 65537)
5. Compute `d = e⁻¹ mod φ(n)` (private exponent)
6. Public key: `(n, e)`, Private key: `(n, d, p, q, dP, dQ, qInv)`

### Encryption/Decryption
- **Encrypt**: `c = m^e mod n`
- **Decrypt**: `m = c^d mod n`
- **CRT Decrypt** (faster):
  - `m1 = c^dP mod p`
  - `m2 = c^dQ mod q`
  - `h = qInv × (m1 - m2) mod p`
  - `m = m2 + h × q`

### Signing/Verification
- **Sign**: `s = (pad(hash(m)))^d mod n`
- **Verify**: `m' = s^e mod n`, check `m' == pad(hash(m))`

## Security Considerations

1. **Key Size**: Use 2048+ bit keys for modern security
2. **Padding**: Always use proper padding (OAEP for encryption, PSS/PKCS#1 for signing)
3. **Random Numbers**: Use cryptographically secure RNG in production
4. **Timing**: Implement constant-time operations where possible
5. **Prime Selection**: Ensure `p ≠ q` and `|p - q|` is large enough
6. **Public Exponent**: 65537 is recommended (balance of security and performance)

## Performance Characteristics

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| Key Generation | O(k³) | k = key bits; dominated by prime testing |
| Encryption | O(k²) | Public exponent usually small (65537) |
| Decryption | O(k³) | Without CRT optimization |
| Decryption (CRT) | O(k²) | ~4x faster than standard |
| Signing | O(k³) | Uses private exponent |
| Verification | O(k²) | Uses public exponent |

**Estimates** (Pure Simple, interpreted):
- 2048-bit key generation: ~10-30 seconds
- 2048-bit encryption: ~100ms
- 2048-bit decryption (CRT): ~400ms
- 2048-bit signing: ~400ms
- 2048-bit verification: ~100ms

## Module Dependencies

```
types.spl (no dependencies)
  ├─ modular.spl
  ├─ random.spl
  ├─ primality.spl (→ modular, random)
  ├─ key_gen.spl (→ modular, primality)
  ├─ byte_conversion.spl
  └─ padding.spl (→ random)
      ├─ encrypt.spl (→ modular, key_gen, byte_conversion, padding)
      ├─ sign.spl (→ modular, key_gen, byte_conversion, padding, encrypt)
      └─ utilities.spl (→ key_gen, byte_conversion)
```

## Example Usage

```simple
import src.std.rsa_utils as rsa

# Generate 2048-bit keypair
val keypair = rsa.generate_rsa_keypair(2048)
val public_key = array.get(keypair, 0)
val private_key = array.get(keypair, 1)

# Encrypt/Decrypt
val ciphertext = rsa.rsa_encrypt("Hello, World!", public_key)
val plaintext = rsa.rsa_decrypt(ciphertext, private_key)

# Sign/Verify
val signature = rsa.rsa_sign("Important message", private_key)
val valid = rsa.rsa_verify("Important message", signature, public_key)

# Export keys
val pem_public = rsa.encode_public_key(public_key)
val pem_private = rsa.encode_private_key(private_key)
```

## Implementation Notes

- **BigInt Base**: 2^30 (30 bits per limb) to avoid overflow in i64 multiplication
- **Little-Endian**: BigInt limbs stored least-significant first
- **Normalization**: Leading zeros removed after operations
- **Division**: Long division algorithm for BigInt
- **Primality**: 40 rounds of Miller-Rabin (2^-80 error probability)
- **CRT**: Chinese Remainder Theorem for 4x decryption speedup

## Future Enhancements

- [ ] OAEP padding (optimal asymmetric encryption)
- [ ] PSS padding (probabilistic signature scheme)
- [ ] Multi-prime RSA (>2 primes for faster operations)
- [ ] Karatsuba/Toom-Cook multiplication
- [ ] Montgomery reduction for modular arithmetic
- [ ] Batch primality testing
- [ ] Constant-time operations
- [ ] Hardware acceleration (if available)

## Testing

See `test/std/rsa_utils_spec.spl` for comprehensive test suite covering:
- BigInt arithmetic edge cases
- Primality testing accuracy
- Key generation validity
- Encryption/decryption round-trips
- Signature verification
- Padding validation
- Performance benchmarks
