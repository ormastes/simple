# Cryptographic Utilities Module

Pure Simple implementation of cryptographic hash functions and utilities.
No FFI, no external dependencies - all algorithms implemented from scratch following official specifications.

## Security Guidelines

**Recommended Algorithms:**
- **SHA-256**: General-purpose hashing (32 bytes / 256 bits)
- **SHA-512**: Higher security hashing (64 bytes / 512 bits)
- **HMAC-SHA256/512**: Message authentication
- **PBKDF2**: Password hashing with 100,000+ iterations

**Deprecated Algorithms (Legacy Support Only):**
- **SHA-1**: Cryptographically broken - DO NOT use for security
- **MD5**: Cryptographically broken - DO NOT use for security

## Module Structure

### types.spl (272 lines)
Core utilities for cryptographic operations:
- **Bit operations**: `rotr32`, `rotr64`, `rotl32`, `shr32`, `shr64`
- **Modular arithmetic**: `add_mod32`, `add_mod64`
- **Byte/hex conversion**: `bytes_to_hex`, `hex_to_bytes`, `text_to_bytes`, `bytes_to_text`
- **Hash utilities**: `hash_to_upper_hex`, `xor_bytes`, `truncate_hash`

### sha256.spl (388 lines)
SHA-256 hash implementation:
- **Constants**: `sha256_k_constants`, `sha256_initial_hash`
- **Functions**: `sha256_ch`, `sha256_maj`, `sha256_sigma0`, `sha256_sigma1`
- **Context**: `create_sha256_context`, `sha256_update`, `sha256_finalize`, `sha256_reset`
- **Public API**: `sha256`, `sha256_bytes`, `sha256_hex`, `sha256_hex_upper`
- **Utilities**: `double_sha256`, `hash_stream_sha256`

### sha512.spl (372 lines)
SHA-512 hash implementation:
- **Constants**: `sha512_k_constants`, `sha512_initial_hash`
- **Functions**: `sha512_ch`, `sha512_maj`, `sha512_sigma0`, `sha512_sigma1`
- **Context**: `create_sha512_context`, `sha512_update`, `sha512_finalize`, `sha512_reset`
- **Public API**: `sha512`, `sha512_bytes`, `sha512_hex`, `sha512_hex_upper`
- **Utilities**: `hash_stream_sha512`

### legacy_hash.spl (451 lines)
Deprecated hash algorithms (SHA-1 and MD5):
- **SHA-1**: `sha1`, `sha1_bytes`, `sha1_hex` (DEPRECATED)
- **MD5**: `md5`, `md5_bytes`, `md5_hex` (INSECURE)
- WARNING: Only for legacy system compatibility

### hmac.spl (220 lines)
HMAC (Hash-based Message Authentication Code):
- **HMAC-SHA256**: `hmac_sha256`, `hmac_sha256_bytes`
- **HMAC-SHA512**: `hmac_sha512`, `hmac_sha512_bytes`
- **HMAC-SHA1**: `hmac_sha1`, `hmac_sha1_bytes` (DEPRECATED)
- **Generic**: `hmac_with_algorithm`

### pbkdf2.spl (165 lines)
PBKDF2 password-based key derivation:
- **PBKDF2-SHA256**: `pbkdf2_sha256`, `pbkdf2_sha256_bytes`
- **PBKDF2-SHA512**: `pbkdf2_sha512`, `pbkdf2_sha512_bytes`
- **Generic**: `pbkdf2_with_algorithm`
- **Utilities**: `get_recommended_pbkdf2_iterations` (returns 100,000)

### utilities.spl (176 lines)
High-level cryptographic utilities:
- **Security**: `constant_time_compare`, `secure_compare`, `verify_hash`
- **Passwords**: `hash_password`, `verify_password`, `generate_salt`
- **Checksums**: `create_checksum`, `verify_checksum`, `compare_hex_hashes`
- **Metadata**: `get_hash_length`, `get_block_size`, `is_secure_algorithm`
- **Selection**: `hash_with_algorithm`, `get_recommended_algorithm`

## Usage Examples

### Basic Hashing

```simple
mod crypto_utils

# SHA-256 (recommended)
val hash = sha256_hex("hello world")
print hash  # "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9"

# SHA-512
val hash512 = sha512_hex("hello world")

# Streaming hash (for large data)
val chunks = ["chunk1", "chunk2", "chunk3"]
val stream_hash = hash_stream_sha256(chunks)
```

### Message Authentication (HMAC)

```simple
mod crypto_utils

val key = "secret_key"
val message = "important message"
val mac = hmac_sha256(key, message)
val mac_hex = bytes_to_hex(mac)

# Verify
val is_valid = secure_compare(mac, hmac_sha256(key, message))
```

### Password Hashing

```simple
mod crypto_utils

val password = "user_password"
val salt = generate_salt(16)  # In production, use cryptographically secure RNG

# Hash password (PBKDF2-SHA256, 100,000 iterations)
val hash = hash_password(password, salt)

# Verify password
val is_correct = verify_password(password, salt, hash)
```

### Custom PBKDF2

```simple
mod crypto_utils

val password_bytes = text_to_bytes("password")
val salt_bytes = text_to_bytes("random_salt")
val iterations = 100000
val key_length = 32

val derived_key = pbkdf2_sha256_bytes(password_bytes, salt_bytes, iterations, key_length)
```

### Checksums

```simple
mod crypto_utils

val data = "file contents"
val checksum = create_checksum(data)  # 8-char hex (4 bytes)

# Verify
val is_valid = verify_checksum(data, checksum)
```

### Constant-Time Comparison (Prevent Timing Attacks)

```simple
mod crypto_utils

val hash1 = sha256("data1")
val hash2 = sha256("data2")

# NEVER use hash1 == hash2 for security-critical comparisons
# Use constant-time comparison instead:
val is_match = constant_time_compare(hash1, hash2)
```

## Algorithm Selection

```simple
mod crypto_utils

# Get recommended algorithm
val algo = get_recommended_algorithm()  # "sha256"

# Check if algorithm is secure
val is_secure = is_secure_algorithm("sha256")  # true
val is_md5_secure = is_secure_algorithm("md5")  # false

# Get hash properties
val hash_len = get_hash_length("sha256")  # 32 bytes
val block_size = get_block_size("sha512")  # 128 bytes

# Hash with selected algorithm
val hash = hash_with_algorithm("data", "sha256")
```

## Security Best Practices

1. **Use SHA-256 or SHA-512** for new applications
2. **Never use MD5 or SHA-1** for security purposes
3. **Use HMAC** for message authentication, not plain hashing
4. **Use PBKDF2 with high iteration count** (100,000+) for passwords
5. **Use constant-time comparison** to prevent timing attacks
6. **Use cryptographically secure RNG** for salt generation in production
7. **Store hash algorithm identifier** with hashes for future migration

## Refactoring Summary

**Original**: crypto_utils.spl (1,677 lines)

**Refactored into 7 modules**:
- types.spl (272 lines)
- sha256.spl (388 lines)
- sha512.spl (372 lines)
- legacy_hash.spl (451 lines)
- hmac.spl (220 lines)
- pbkdf2.spl (165 lines)
- utilities.spl (176 lines)

**Total**: 2,044 lines (includes additional documentation and organization)

**Benefits**:
- Focused modules with clear responsibilities
- Easier to understand and maintain
- Better separation of secure vs deprecated algorithms
- Improved code navigation
- Backward compatible (all original functions still accessible)
