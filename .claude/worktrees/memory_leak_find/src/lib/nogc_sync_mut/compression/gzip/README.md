# GZIP Compression Module

**Refactored:** 2026-02-12
**Original:** `src/lib/nogc_sync_mut/compression/gzip/` (1,891 lines)
**New Structure:** 8 focused modules (~150-400 lines each)

---

## Overview

Pure Simple implementation of GZIP compression format (RFC 1952) and DEFLATE algorithm (RFC 1951). Combines LZ77 sliding window compression with Huffman coding for efficient data compression.

---

## Module Structure

### Core Modules

| Module | Lines | Purpose |
|--------|-------|---------|
| `types.spl` | ~120 | Constants, block types, compression levels |
| `crc.spl` | ~100 | CRC32 checksum calculation and verification |
| `header.spl` | ~150 | GZIP header/footer parsing and creation |
| `lz77.spl` | ~280 | LZ77 sliding window compression |
| `huffman.spl` | ~320 | Huffman tree construction and coding |
| `deflate.spl` | ~400 | DEFLATE compression algorithm |
| `inflate.spl` | ~380 | DEFLATE decompression algorithm |
| `stream.spl` | ~150 | Stream operations, bit packing, utilities |
| `compress.spl` | ~600 | Main compression API and analysis |

---

## Usage

### Import

```simple
# Via facade (backward compatible)
mod gzip_utils

# Or directly from modules
mod compression.gzip.compress
mod compression.gzip.crc
```

### Basic Compression

```simple
# Compress with default level (6)
val data = [72, 101, 108, 108, 111]  # "Hello"
val compressed = compress_gzip(data)

# Decompress
val decompressed = decompress_gzip(compressed)

# Compress with specific level (0-9)
val fast = compress_gzip_level(data, LEVEL_FAST)  # Level 1
val best = compress_gzip_level(data, LEVEL_BEST)  # Level 9
```

### Validation and Metadata

```simple
# Validate GZIP data
if validate_gzip(compressed):
    print "Valid GZIP format"

# Extract metadata
val metadata = get_gzip_metadata(compressed)
# Returns: [timestamp, os, extra_flags, crc, size]

# Check if data is compressed
if is_gzip_compressed(data):
    print "Already compressed"
```

### CRC32 Checksums

```simple
# Calculate CRC32
val crc = calculate_crc32(data)

# Verify checksum
if verify_crc32(data, expected_crc):
    print "Checksum valid"

# Stream CRC calculation
val chunks = [[1, 2, 3], [4, 5, 6]]
val crc = crc32_chunked(chunks)
```

### Stream Operations

```simple
# Compress multiple chunks
val chunks = [chunk1, chunk2, chunk3]
val compressed = stream_compress_gzip(chunks, LEVEL_DEFAULT)

# Split data into optimal blocks
val blocks = split_into_blocks(large_data)

# Merge blocks back
val merged = merge_blocks(blocks)
```

### Analysis and Statistics

```simple
# Get compression ratio
val ratio = get_compression_ratio(orig_size, comp_size)

# Get space savings percentage
val savings = get_space_savings(orig_size, comp_size)

# Analyze data compressibility
val analysis = analyze_data(data)
# Returns: [size, unique_bytes, entropy, freq_distribution]

# Find repeated patterns
val patterns = find_patterns(data, pattern_length: 4)

# Suggest optimal compression level
val level = gzip_suggest_level(data)

# Compare all compression levels
val results = gzip_compare_levels(data)
# Returns: [[level, size, ratio], ...]
```

---

## Algorithm Details

### DEFLATE Compression Pipeline

1. **LZ77 Sliding Window** (`lz77.spl`)
   - 32KB sliding window dictionary
   - Find longest matches (3-258 bytes)
   - Encode as literals or (distance, length) pairs
   - Adjusts search depth based on compression level

2. **Huffman Coding** (`huffman.spl`)
   - Build frequency table from LZ77 tokens
   - Construct optimal Huffman tree
   - Generate variable-length codes
   - Supports fixed and dynamic codes

3. **DEFLATE Block Creation** (`deflate.spl`)
   - Three block types: stored, fixed Huffman, dynamic Huffman
   - Maps length/distance to DEFLATE codes
   - Creates RFC 1951 compliant blocks

4. **GZIP Wrapper** (`header.spl`, `compress.spl`)
   - Add GZIP header (magic bytes, flags, timestamp)
   - Add footer (CRC32 checksum, uncompressed size)
   - Creates RFC 1952 compliant format

### DEFLATE Decompression Pipeline

1. **Header Parsing** (`header.spl`)
   - Validate magic bytes (0x1f, 0x8b)
   - Extract compression method, flags, metadata
   - Skip optional fields (filename, comment, extra)

2. **Block Decompression** (`inflate.spl`)
   - Detect block type (stored/fixed/dynamic)
   - Decompress based on block type
   - Handle multi-block streams

3. **Footer Validation** (`header.spl`)
   - Verify CRC32 checksum
   - Verify uncompressed size
   - Ensure data integrity

---

## Compression Levels

| Level | Name | Speed | Ratio | Use Case |
|-------|------|-------|-------|----------|
| 0 | `LEVEL_NONE` | Fastest | 1.0 | No compression (store only) |
| 1 | `LEVEL_FAST` | Fast | 0.7 | Real-time compression |
| 6 | `LEVEL_DEFAULT` | Medium | 0.5 | Balanced compression |
| 9 | `LEVEL_BEST` | Slow | 0.4 | Maximum compression |

Higher levels search more extensively in the sliding window:
- Level 1: 128 byte search
- Level 6+: 4096 byte search
- Level 9: 32768 byte search (full window)

---

## Constants

### GZIP Format
```simple
GZIP_MAGIC1 = 0x1f       # First magic byte
GZIP_MAGIC2 = 0x8b       # Second magic byte
CM_DEFLATE = 8           # Compression method
```

### Operating Systems
```simple
OS_FAT = 0               # FAT filesystem
OS_UNIX = 3              # Unix
OS_NTFS = 11             # NTFS filesystem
OS_UNKNOWN = 255         # Unknown
```

### GZIP Flags
```simple
FLAG_TEXT = 1            # Text file
FLAG_HCRC = 2            # Header CRC
FLAG_EXTRA = 4           # Extra field
FLAG_NAME = 8            # Original filename
FLAG_COMMENT = 16        # Comment
```

### DEFLATE Parameters
```simple
WINDOW_SIZE = 32768      # 32KB sliding window
MIN_MATCH = 3            # Minimum match length
MAX_MATCH = 258          # Maximum match length
MAX_DISTANCE = 32768     # Maximum backward distance
```

### Block Types
```simple
BLOCK_STORED = 0         # Uncompressed
BLOCK_FIXED = 1          # Fixed Huffman codes
BLOCK_DYNAMIC = 2        # Dynamic Huffman codes
```

---

## Design Decisions

### Why Split This File?

**Original Issues:**
- 1,891 lines in single file
- 9 distinct functional categories
- Difficult to navigate and maintain
- No clear module boundaries

**Benefits of Splitting:**
- Each module has single clear purpose
- Easier to test individual components
- Better code organization
- Maintains backward compatibility via facade

### Module Dependencies

```
types.spl (no dependencies)
  ├─ crc.spl
  ├─ header.spl → crc.spl
  ├─ lz77.spl
  ├─ huffman.spl
  ├─ deflate.spl → huffman.spl
  ├─ inflate.spl → huffman.spl
  ├─ stream.spl → crc.spl, header.spl, lz77.spl, deflate.spl
  └─ compress.spl → (all above)
```

### Backward Compatibility

The facade pattern ensures 100% backward compatibility:
- All existing imports work unchanged
- All function names remain the same
- Same API, same behavior
- Only internal organization changed

---

## Testing

Run GZIP tests:
```bash
bin/simple test test/std/gzip_utils_spec.spl
```

Test specific functionality:
```bash
# Test compression/decompression
bin/simple test test/std/gzip_utils_spec.spl --grep "compress"

# Test CRC32
bin/simple test test/std/gzip_utils_spec.spl --grep "crc"

# Test LZ77
bin/simple test test/std/gzip_utils_spec.spl --grep "lz77"
```

---

## Performance Characteristics

### Time Complexity

| Operation | Complexity | Notes |
|-----------|------------|-------|
| LZ77 compression | O(n × w) | n=data size, w=window search depth |
| Huffman tree build | O(n log n) | n=unique symbols |
| Huffman encode | O(n × h) | n=data size, h=tree height |
| CRC32 | O(n) | Linear in data size |
| Decompression | O(n) | Linear in compressed size |

### Space Complexity

| Component | Space | Notes |
|-----------|-------|-------|
| Sliding window | 32KB | Fixed size |
| Huffman tree | O(symbols) | Typically < 1KB |
| Token buffer | O(n) | Proportional to input |
| CRC32 table | 16 entries | Fixed, simplified |

---

## Limitations

### Current Implementation

1. **Simplified CRC32:** Uses 16-entry lookup table instead of full 256-entry table
2. **Fixed Huffman Only:** Dynamic Huffman blocks not yet implemented
3. **No Dictionary:** Pre-compression dictionaries not supported
4. **No Multi-threading:** Compression is single-threaded
5. **Memory-based:** All data in memory (no true streaming)

### Future Enhancements

- [ ] Full 256-entry CRC32 lookup table
- [ ] Dynamic Huffman code generation
- [ ] Pre-compression dictionary support
- [ ] True streaming compression (bounded memory)
- [ ] Multi-block parallel compression
- [ ] ZLIB format support (RFC 1950)
- [ ] ZIP archive support

---

## References

- **RFC 1951:** DEFLATE Compressed Data Format Specification
- **RFC 1952:** GZIP File Format Specification
- **RFC 1950:** ZLIB Compressed Data Format Specification

---

## Related Modules

- `compression_utils.spl` - General compression utilities
- `hash_utils.spl` - Other hashing algorithms
- `file_system_utils.spl` - File I/O for compressed files

---

**Refactored by:** Claude Sonnet 4.5
**Date:** February 12, 2026
**Pattern:** Facade pattern (backward compatible)
