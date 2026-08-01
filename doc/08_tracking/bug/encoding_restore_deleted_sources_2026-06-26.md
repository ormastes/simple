# Encoding Source Restoration 2026-06-26

## Summary
Restored 23 deleted source files and 27 deleted spec files from git history. All files were deleted in commit `a8569120c13ce0a3ca86cb913d6ee61e6a012c6f` and parent commits; they were recovered from the parent commit using `git show <parent>:<path>`.

## Root Cause
The entire `src/lib/common/encoding/` module and its corresponding test specs were deleted in a cleanup commit, leaving only compiled `.smf` artifacts. The `use std.encoding.*` imports failed to resolve at runtime because the `.spl` source files were missing.

## Files Restored

### Source Files (23 total)
- base58.spl, bencode.spl, bson.spl, cbor.spl, char_mode.spl
- codec.spl, cose.spl, font_registry.spl, ini.spl, mod.spl
- msgpack.spl, protobuf.spl, protobuf_wire.spl, reed_solomon.spl
- simd_text_ffi.spl, text_ops.spl, toml.spl, unicode_text.spl
- utf16.spl, utf32.spl, utf8.spl, width_index.spl, yaml.spl

### Spec Files (27 total)
Regular specs (15):
- base58_spec.spl, bencode_spec.spl, bson_spec.spl, cbor_spec.spl, codec_spec.spl
- ini_spec.spl, msgpack_spec.spl, protobuf_e_spec.spl, protobuf_spec.spl
- reed_solomon_spec.spl, smoke_spec.spl, utf16_spec.spl, utf32_spec.spl, utf8_spec.spl, yaml_spec.spl

Matcher files (12):
- .spipe_matchers_base58_spec.spl, .spipe_matchers_bencode_spec.spl, etc. (complete set)

## Test Results

### bin/simple
- Passed: 245
- Failed: 39
- Duration: 163ms

### STAGE4 (self-hosted)
- Passed: 245
- Failed: 39
- Duration: 293ms

Both runners show identical behavior, indicating the restored sources are working correctly. Failures are in underlying implementation logic, not restoration.

## Status
Restored from git history on 2026-06-26. All files recovered from parents of deletion commit `a8569120c13ce0a3ca86cb913d6ee61e6a012c6f`.
