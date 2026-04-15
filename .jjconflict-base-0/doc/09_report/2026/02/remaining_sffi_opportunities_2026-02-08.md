# Remaining SFFI Wrapper Opportunities

**Date:** 2026-02-08
**Analysis:** Features that can be unblocked with SFFI wrappers
**Total Opportunities:** ~120 tests can be unblocked

---

## Executive Summary

After completing 7 major SFFI wrappers (Game Engine stack, JIT, HTTP), there are still **~120 skip tests** that can be unblocked by adding SFFI wrappers for common system libraries.

**Already Complete (7 wrappers):**
- ✅ Physics (Rapier2D) - 620 lines
- ✅ Windowing (Winit) - 750 lines
- ✅ Graphics (Lyon) - 700 lines
- ✅ Audio (Rodio) - 550 lines
- ✅ Gamepad (Gilrs) - 431 lines
- ✅ JIT (Cranelift) - 486 lines
- ✅ HTTP (reqwest/warp) - 650 lines

**Remaining Opportunities (10 categories):**

---

## 1. Cryptography & Hashing 🔴 HIGH PRIORITY

**Unblocks:** ~47 tests
**Impact:** Security, data integrity, authentication
**Lines:** ~400-500 (wrapper + tests)
**Crate:** `ring` or `sha2`, `aes`, `rsa`

**Missing Functions:**
```simple
# Hashing (SHA-256 exists, but incomplete)
hash_sha1(data: text) -> text
hash_sha256(data: text) -> text  # ✅ Already exists
hash_sha512(data: text) -> text
hash_md5(data: text) -> text
hash_blake3(data: text) -> text

# HMAC
hmac_sha256(key: text, data: text) -> text
hmac_sha512(key: text, data: text) -> text

# Encryption (AES)
encrypt_aes256(key: text, data: text) -> text
decrypt_aes256(key: text, encrypted: text) -> text

# RSA
rsa_generate_keypair(bits: i64) -> (text, text)  # (public, private)
rsa_encrypt(public_key: text, data: text) -> text
rsa_decrypt(private_key: text, encrypted: text) -> text

# Password hashing
password_hash(password: text) -> text  # bcrypt/argon2
password_verify(password: text, hash: text) -> bool

# Random bytes
random_bytes(length: i64) -> [i64]
random_string(length: i64) -> text
```

**Use Cases:**
- Password hashing for authentication
- Data encryption at rest
- API signature verification
- Token generation
- Secure random IDs

**Priority:** 🔴 **HIGH** - Security is critical

---

## 2. Compression & Archives 🟡 MEDIUM PRIORITY

**Unblocks:** ~25 tests
**Impact:** File operations, data transfer, backups
**Lines:** ~350-450 (wrapper + tests)
**Crate:** `flate2`, `zip`, `tar`

**Missing Functions:**
```simple
# Gzip
gzip_compress(data: text) -> [i64]
gzip_decompress(data: [i64]) -> text
gzip_file(input_path: text, output_path: text) -> bool

# Zip archives
zip_create(archive_path: text) -> ZipArchive
zip_add_file(archive: ZipArchive, file_path: text, name: text) -> bool
zip_add_dir(archive: ZipArchive, dir_path: text) -> bool
zip_close(archive: ZipArchive) -> bool

zip_extract(archive_path: text, output_dir: text) -> bool
zip_list_files(archive_path: text) -> [text]
zip_extract_file(archive_path: text, file_name: text, output_path: text) -> bool

# Tar archives
tar_create(archive_path: text, files: [text]) -> bool
tar_extract(archive_path: text, output_dir: text) -> bool
tar_list(archive_path: text) -> [text]

# Compression level control
compress_data(data: text, level: i64) -> [i64]  # level 0-9
decompress_data(data: [i64]) -> text
```

**Use Cases:**
- File compression for storage
- Archive creation/extraction
- Backup systems
- Data transfer optimization
- Package management

**Priority:** 🟡 **MEDIUM** - Useful for many applications

---

## 3. Regular Expressions 🟡 MEDIUM PRIORITY

**Unblocks:** ~13 tests
**Impact:** Text processing, validation, parsing
**Lines:** ~300-400 (wrapper + tests)
**Crate:** `regex`

**Missing Functions:**
```simple
# Pattern matching
regex_match(pattern: text, text: text) -> bool
regex_find(pattern: text, text: text) -> text
regex_find_all(pattern: text, text: text) -> [text]

# Capture groups
regex_captures(pattern: text, text: text) -> [text]

# Replace
regex_replace(pattern: text, text: text, replacement: text) -> text
regex_replace_all(pattern: text, text: text, replacement: text) -> text

# Split
regex_split(pattern: text, text: text) -> [text]

# Validation helpers
is_email(text: text) -> bool
is_url(text: text) -> bool
is_ipv4(text: text) -> bool
is_uuid(text: text) -> bool

# Compiled regex for performance
regex_compile(pattern: text) -> Regex
regex_test(regex: Regex, text: text) -> bool
regex_free(regex: Regex)
```

**Use Cases:**
- Input validation
- Text parsing
- Log analysis
- Data extraction
- Configuration parsing

**Priority:** 🟡 **MEDIUM** - Very common need

---

## 4. Process Info 🟡 MEDIUM PRIORITY

**Unblocks:** ~15 tests (from earlier analysis)
**Impact:** System utilities, monitoring
**Lines:** ~150-200 (wrapper + tests)
**Crate:** Standard library (libc)

**Missing Functions:**
```simple
# Process info (rt_getpid exists, but incomplete)
process_pid() -> i64  # ✅ rt_getpid exists
process_parent_pid() -> i64
process_user_id() -> i64
process_group_id() -> i64
process_name() -> text
process_path() -> text
process_args() -> [text]
process_env_vars() -> [(text, text)]

# System info
system_cpu_count() -> i64
system_memory_total() -> i64
system_memory_free() -> i64
system_uptime() -> i64
system_load_average() -> (f64, f64, f64)

# User info
user_name() -> text
user_home_dir() -> text
user_shell() -> text
```

**Use Cases:**
- System monitoring
- Process management
- Resource tracking
- Debugging tools
- Admin utilities

**Priority:** 🟡 **MEDIUM** - Useful for system tools

---

## 5. Date/Time Extended 🟢 LOW PRIORITY

**Unblocks:** ~9 tests
**Impact:** Scheduling, logging, timestamps
**Lines:** ~250-350 (wrapper + tests)
**Crate:** `chrono`

**Existing:** `rt_time_now_unix_micros` ✅

**Missing Functions:**
```simple
# Current time (basic exists, need extended)
time_now_iso8601() -> text
time_now_rfc3339() -> text

# Parsing
time_parse(format: text, string: text) -> i64
time_parse_iso8601(string: text) -> i64

# Formatting
time_format(timestamp: i64, format: text) -> text
time_to_iso8601(timestamp: i64) -> text

# Components
time_year(timestamp: i64) -> i64
time_month(timestamp: i64) -> i64
time_day(timestamp: i64) -> i64
time_hour(timestamp: i64) -> i64
time_minute(timestamp: i64) -> i64
time_second(timestamp: i64) -> i64

# Timezone
time_to_utc(timestamp: i64) -> i64
time_to_local(timestamp: i64) -> i64
time_timezone_offset() -> i64

# Duration
duration_days(days: i64) -> i64
duration_hours(hours: i64) -> i64
duration_minutes(minutes: i64) -> i64
```

**Use Cases:**
- Timestamp formatting
- Date parsing
- Scheduling
- Log timestamps
- Time zone conversion

**Priority:** 🟢 **LOW** - Basic time exists, this is extended

---

## 6. File System Extended ⚪ VERY LOW

**Unblocks:** ~4 tests
**Impact:** Advanced file operations
**Lines:** ~200-300 (wrapper + tests)
**Crate:** `notify`, `nix`

**Missing Functions:**
```simple
# File watching
file_watch_create(path: text) -> FileWatcher
file_watch_poll(watcher: FileWatcher) -> FileEvent
file_watch_close(watcher: FileWatcher)

# Symlinks
symlink_create(target: text, link: text) -> bool
symlink_read(path: text) -> text
is_symlink(path: text) -> bool

# Permissions (Unix)
file_chmod(path: text, mode: i64) -> bool
file_chown(path: text, uid: i64, gid: i64) -> bool
file_get_permissions(path: text) -> i64

# Extended attributes
file_set_attr(path: text, key: text, value: text) -> bool
file_get_attr(path: text, key: text) -> text
```

**Use Cases:**
- File system monitoring
- Symbolic link management
- Permission management
- Extended attributes

**Priority:** ⚪ **VERY LOW** - Niche use cases

---

## 7. Database Connections 🔴 HIGH PRIORITY

**Unblocks:** 0 tests currently (but high value)
**Impact:** Data persistence, web apps
**Lines:** ~600-800 per database (wrapper + tests)
**Crate:** `rusqlite`, `postgres`, `mysql`, `redis`

**Missing Functions:**

**SQLite:**
```simple
sqlite_open(path: text) -> Database
sqlite_execute(db: Database, sql: text) -> bool
sqlite_query(db: Database, sql: text) -> [[text]]
sqlite_prepare(db: Database, sql: text) -> Statement
sqlite_bind(stmt: Statement, index: i64, value: text) -> bool
sqlite_step(stmt: Statement) -> bool
sqlite_get(stmt: Statement, index: i64) -> text
sqlite_close(db: Database)
```

**PostgreSQL:**
```simple
postgres_connect(url: text) -> Database
postgres_execute(db: Database, sql: text, params: [text]) -> bool
postgres_query(db: Database, sql: text, params: [text]) -> [[text]]
postgres_close(db: Database)
```

**MySQL:**
```simple
mysql_connect(url: text) -> Database
mysql_execute(db: Database, sql: text, params: [text]) -> bool
mysql_query(db: Database, sql: text, params: [text]) -> [[text]]
mysql_close(db: Database)
```

**Redis:**
```simple
redis_connect(url: text) -> Redis
redis_get(redis: Redis, key: text) -> text
redis_set(redis: Redis, key: text, value: text) -> bool
redis_delete(redis: Redis, key: text) -> bool
redis_exists(redis: Redis, key: text) -> bool
redis_expire(redis: Redis, key: text, seconds: i64) -> bool
redis_close(redis: Redis)
```

**Use Cases:**
- Data persistence
- Web applications
- Caching (Redis)
- Session storage
- Relational data

**Priority:** 🔴 **HIGH** - Critical for real applications

---

## 8. Random/UUID ⚪ VERY LOW

**Unblocks:** ~2 tests
**Impact:** ID generation
**Lines:** ~100-150 (wrapper + tests)
**Crate:** `uuid`, `rand`

**Missing Functions:**
```simple
# UUID
uuid_v4() -> text  # Random UUID
uuid_v5(namespace: text, name: text) -> text  # Named UUID

# Random (crypto-safe already in crypto section)
random_int(min: i64, max: i64) -> i64
random_float() -> f64
random_choice(items: [text]) -> text
random_shuffle(items: [text]) -> [text]
```

**Use Cases:**
- Unique ID generation
- Random selection
- Shuffling

**Priority:** ⚪ **VERY LOW** - Can use crypto random

---

## 9. Image Processing 🟡 MEDIUM PRIORITY

**Unblocks:** 0 tests currently (but valuable)
**Impact:** Graphics applications, thumbnails
**Lines:** ~500-700 (wrapper + tests)
**Crate:** `image`

**Missing Functions:**
```simple
# Image loading/saving
image_load(path: text) -> Image
image_save(image: Image, path: text) -> bool
image_free(image: Image)

# Image info
image_width(image: Image) -> i64
image_height(image: Image) -> i64
image_format(path: text) -> text  # "png", "jpeg", etc.

# Transformations
image_resize(image: Image, width: i64, height: i64) -> Image
image_crop(image: Image, x: i64, y: i64, width: i64, height: i64) -> Image
image_rotate(image: Image, degrees: i64) -> Image
image_flip_horizontal(image: Image) -> Image
image_flip_vertical(image: Image) -> Image

# Filters
image_grayscale(image: Image) -> Image
image_blur(image: Image, sigma: f64) -> Image
image_brighten(image: Image, value: i64) -> Image
image_contrast(image: Image, value: f64) -> Image

# Conversion
image_to_bytes(image: Image) -> [i64]
image_from_bytes(bytes: [i64], width: i64, height: i64) -> Image
```

**Use Cases:**
- Thumbnail generation
- Image processing
- Format conversion
- Photo editing
- Graphics tools

**Priority:** 🟡 **MEDIUM** - Useful for many apps

---

## 10. LLVM IR Export ⚪ VERY LOW

**Unblocks:** ~5 tests (from earlier analysis)
**Impact:** Compiler developers
**Lines:** ~200-300 (wrapper + tests)
**Crate:** `inkwell` (optional LLVM)

**Already Declared:** `rt_compile_to_llvm_ir` ✅ (but not implemented)

**Missing Implementation:**
```simple
# Already in SFFI wrapper but not implemented:
compile_to_llvm_ir(source: text, output: text) -> bool
compile_to_llvm_bitcode(source: text, output: text) -> bool
optimize_llvm_ir(ir_path: text, opt_level: i64) -> bool
```

**Use Cases:**
- Compiler research
- Optimization analysis
- Advanced codegen

**Priority:** ⚪ **VERY LOW** - Niche use case

---

## Priority Summary

### 🔴 High Priority (Should Do Next)

1. **Cryptography** (~47 tests, ~400-500 lines)
   - Critical for security
   - Password hashing, encryption, signatures
   - **High value, common need**

2. **Database Connections** (0 tests currently, but critical)
   - SQLite, PostgreSQL, MySQL, Redis
   - Essential for real applications
   - **High value, ~600-800 lines per DB**

### 🟡 Medium Priority (Good to Have)

3. **Compression** (~25 tests, ~350-450 lines)
   - Zip, gzip, tar archives
   - File compression/decompression

4. **Regular Expressions** (~13 tests, ~300-400 lines)
   - Text processing, validation
   - Very common need

5. **Process Info** (~15 tests, ~150-200 lines)
   - System monitoring, debugging
   - Completes process management

6. **Image Processing** (0 tests, ~500-700 lines)
   - Graphics, thumbnails
   - High value for GUI apps

### 🟢 Low Priority (Nice to Have)

7. **Date/Time Extended** (~9 tests, ~250-350 lines)
   - Advanced date/time operations
   - Basic time already exists

### ⚪ Very Low Priority (Optional)

8. **File System Extended** (~4 tests, ~200-300 lines)
   - File watching, symlinks
   - Niche use cases

9. **Random/UUID** (~2 tests, ~100-150 lines)
   - Can use crypto random instead

10. **LLVM IR Export** (~5 tests, ~200-300 lines)
    - Compiler developers only

---

## Implementation Roadmap

### Phase 1: Security & Data (HIGH)
**Lines:** ~1,400-1,800
**Time:** 3-4 days

1. Cryptography wrapper (~400-500 lines)
2. SQLite wrapper (~600-800 lines)
3. PostgreSQL wrapper (~400-500 lines)

**Impact:** Unblocks ~47 tests + enables real applications

### Phase 2: Common Utilities (MEDIUM)
**Lines:** ~1,000-1,300
**Time:** 2-3 days

4. Compression wrapper (~350-450 lines)
5. Regular expressions wrapper (~300-400 lines)
6. Process info wrapper (~150-200 lines)
7. Image processing wrapper (~500-700 lines)

**Impact:** Unblocks ~53 tests + improves developer experience

### Phase 3: Extended Features (LOW)
**Lines:** ~550-800
**Time:** 1-2 days

8. Date/time extended wrapper (~250-350 lines)
9. File system extended wrapper (~200-300 lines)
10. Random/UUID wrapper (~100-150 lines)

**Impact:** Unblocks ~15 tests + completes stdlib

---

## Total Potential

**All 10 Wrappers:**
- **Lines:** ~3,000-4,000 (wrapper + tests + demos)
- **Tests Unblocked:** ~120+
- **Time Estimate:** 6-9 days of work
- **Rust Runtime:** ~2,500-3,000 lines

**Combined with Existing 7 Wrappers:**
- **Total Wrappers:** 17
- **Total Lines:** ~16,000-17,000
- **Total Tests:** ~430+
- **Total Runtime:** ~8,000-8,500 lines Rust

---

## Recommendations

### Immediate Actions (This Week)

1. **Cryptography Wrapper** 🔴
   - Unblocks 47 tests
   - Critical for security
   - ~400-500 lines

2. **SQLite Wrapper** 🔴
   - Essential for data persistence
   - Lightweight, no server needed
   - ~600-800 lines

### Short-Term (Next Week)

3. **Compression Wrapper** 🟡
   - Unblocks 25 tests
   - Very useful
   - ~350-450 lines

4. **Regular Expressions** 🟡
   - Unblocks 13 tests
   - Common need
   - ~300-400 lines

### Long-Term (When Needed)

5. **PostgreSQL/MySQL** 🔴
   - For production apps
   - ~400-500 lines each

6. **Image Processing** 🟡
   - For graphics apps
   - ~500-700 lines

---

## Conclusion

There are **~120 additional tests** that can be unblocked by adding 10 more SFFI wrappers. The highest priority wrappers are:

1. **Cryptography** - Security is critical
2. **SQLite** - Data persistence essential
3. **Compression** - Very useful
4. **Regular Expressions** - Common need

After implementing these 4 high-priority wrappers (~1,850-2,350 lines), Simple will have:
- ✅ Complete game engine
- ✅ JIT compilation
- ✅ HTTP networking
- ✅ Security/crypto
- ✅ Data persistence
- ✅ Compression
- ✅ Text processing

**Total:** 11 major SFFI wrappers covering most common needs!
