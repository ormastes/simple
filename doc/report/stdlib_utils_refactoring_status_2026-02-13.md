# Standard Library Utils Refactoring Status

**Date:** 2026-02-13

## Completed Refactorings

### 1. geometry_utils.spl (1,338 lines → 6 modules)

**Status:** ✅ COMPLETE

**Structure:**
```
src/std/geometry/
├── types.spl          (12 lines) - Constants and types
├── point.spl          (388 lines) - 2D/3D point and vector operations  
├── line.spl           (140 lines) - Line operations and intersections
├── polygon.spl        (176 lines) - Polygon operations and convex hull
├── circle.spl         (383 lines) - Circle, rectangle, triangle operations
└── utilities.spl      (292 lines) - Transformations, bounding boxes, collisions
```

**Facade:** `src/std/geometry_utils.spl` (239 lines)

**Categories:**
- ✅ types - Constants (EPSILON)
- ✅ point - 2D/3D point operations, vector operations
- ✅ line - Line/segment operations
- ✅ polygon - Polygon operations
- ✅ circle - Circle, rectangle, triangle operations  
- ✅ utilities - Transformations, bounding boxes, collisions, misc utilities

### 2. bcrypt_utils.spl (1,335 lines → 6 modules)

**Status:** 🚧 IN PROGRESS

**Planned Structure:**
```
src/std/bcrypt/
├── types.spl          - Constants, S-boxes, magic values
├── hash.spl           - Core bcrypt hashing functions
├── verify.spl         - Password verification and comparison
├── salt.spl           - Salt generation and encoding
├── key_derivation.spl - Blowfish and Eksblowfish implementation
└── utilities.spl      - Helper functions, encoding, parsing
```

**Facade:** `src/std/bcrypt_utils.spl`

**Expected Categories:**
- 🚧 types - Constants, Blowfish P-array and S-boxes
- 🚧 hash - bcrypt_hash, bcrypt_hash_with_salt, format_hash
- 🚧 verify - bcrypt_verify, bcrypt_check, compare_hashes, rehash_if_needed
- 🚧 salt - generate_salt, encode_salt, extract_salt
- 🚧 key_derivation - Blowfish cipher, Eksblowfish key schedule
- 🚧 utilities - Bitwise ops, byte ops, base64, parsing, validation

**Challenges:**
- Deep interdependencies between Blowfish, Eksblowfish, and bcrypt
- Large S-box initialization data (1024 constants)
- Complex bitwise operations and byte manipulation
- State management across encryption rounds

### 3. cbor_utils.spl (1,321 lines → 5 modules)

**Status:** 🚧 IN PROGRESS

**Planned Structure:**
```
src/std/cbor/
├── types.spl          - Major types, constants, type detection
├── encode.spl         - CBOR encoding functions
├── decode.spl         - CBOR decoding functions
├── major_types.spl    - Type detection and validation
└── utilities.spl      - Utilities, diagnostics, hexdump
```

**Facade:** `src/std/cbor_utils.spl`

**Expected Categories:**
- 🚧 types - Major type constants, initial byte encoding
- 🚧 encode - Integer, string, array, map, tag encoding
- 🚧 decode - Integer, string, array, map, tag decoding
- 🚧 major_types - Type detection, validation, size calculation
- 🚧 utilities - Sequences, validation, diagnostic notation, hexdump

**Challenges:**
- Recursive decoding for nested structures
- Indefinite-length encoding support
- Complex type detection and validation
- Large ASCII character mapping tables

## Recommendations for bcrypt and cbor

Due to the high complexity and tight coupling in bcrypt_utils and cbor_utils, I recommend:

1. **Phase 1 (Current):** Create facade with clearly documented sections
2. **Phase 2 (Future):** Gradually extract independent components:
   - bcrypt: Start with utilities (base64, byte ops) → salt → verify → hash → key_derivation
   - cbor: Start with types → utilities → encode → decode → major_types

3. **Testing Strategy:** Ensure tests pass after each extraction

## Summary

- **geometry_utils.spl:** ✅ Successfully refactored into 6 well-organized modules
- **bcrypt_utils.spl:** 🚧 Facade structure prepared, modular extraction pending
- **cbor_utils.spl:** 🚧 Facade structure prepared, modular extraction pending

The facade pattern is in place for all three files, enabling gradual refactoring of bcrypt and cbor while maintaining backward compatibility.
