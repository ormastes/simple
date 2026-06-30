# Bug: std.common.encoding — entire library unimplemented

**Date:** 2026-06-26  
**ID:** encoding_cluster_missing_source  
**Severity:** P2 (cluster of 10+ spec files blocked)

## Affected specs

All specs under `test/01_unit/lib/common/encoding/` report 0/0 discovered
(not 0/1) because the runner ignores dotfile paths. The specs exist only as
`.spipe_matchers_*` private-overlay files:

- `.spipe_matchers_utf8_spec.spl`
- `.spipe_matchers_utf16_spec.spl`
- `.spipe_matchers_utf32_spec.spl`
- `.spipe_matchers_codec_spec.spl`
- `.spipe_matchers_smoke_spec.spl`
- `.spipe_matchers_base58_spec.spl`
- `.spipe_matchers_bencode_spec.spl`
- `.spipe_matchers_bson_spec.spl`
- `.spipe_matchers_ini_spec.spl`
- `.spipe_matchers_msgpack_spec.spl`
- `.spipe_matchers_cbor_spec.spl`
- `.spipe_matchers_protobuf_spec.spl`
- `.spipe_matchers_reed_solomon_spec.spl`
- `.spipe_matchers_yaml_spec.spl`

## Root cause

`src/lib/common/encoding/` does not exist. Only three empty `.smf` stubs
are present (each 179 bytes — main-only header, no symbol content):

- `src/lib/common/encoding.smf`
- `src/lib/common/encoding_utils.smf`
- `src/lib/common/encoding_base.smf`

Every `use std.common.encoding.{utf8,utf16,utf32,codec,protobuf,base58,
bencode,bson,ini,msgpack,cbor,yaml,reed_solomon}` import fails with:
`error: semantic: Cannot resolve module: std.common.encoding.*`

## Premise mismatch

The tracking system records these as "FAIL 0/1 under STAGE4". The actual
result from both seed (`bin/simple test`) and STAGE4 is "Spec files: 0"
because `bin/simple test` only discovers `*_spec.spl` (non-dotfile paths).
The "0/1" count was produced by the `.spipe` private harness (`.spipe/spipe`
is modified in the tree), not by the standard test runner.

## Additional blocker for utf8/codec specs

`text_from_codepoints` and `char_from_codepoint` (imported by `utf8_spec`)
require `text.from_char_code`, which is reported unavailable in interpreter
mode. These would need STAGE4 or compiled mode to verify even after the
source is implemented.

## Modules to implement

| Module | Import path | Notes |
|--------|-------------|-------|
| utf8 | std.common.encoding.utf8 | byte-level decode/encode + text wrappers |
| utf16 | std.common.encoding.utf16 | surrogate-pair handling |
| utf32 | std.common.encoding.utf32 | pure i64/byte arithmetic |
| codec | std.common.encoding.codec | `Encoding` enum, encode/decode/transcode |
| protobuf | std.common.encoding.protobuf | varint, fixed64, tag encode/decode |
| base58 | std.common.encoding.base58 | Bitcoin/IPFS alphabet encode/decode |
| bencode | std.common.encoding.bencode | BitTorrent bencode |
| bson | std.common.encoding.bson | MongoDB BSON |
| ini | std.common.encoding.ini | INI/TOML-style config |
| msgpack | std.common.encoding.msgpack | MessagePack |
| cbor | std.common.encoding.cbor | CBOR (RFC 7049) |
| yaml | std.common.encoding.yaml | YAML (subset) |
| reed_solomon | std.common.encoding.reed_solomon | error-correction codec |

## Fix plan

1. Create `src/lib/common/encoding/` directory.
2. Implement `.spl` source for each module listed above (pure-Simple, no Rust seed changes needed for utf8/utf16/utf32/codec which are pure i64 arithmetic; protobuf+ are larger and may need separate tasks).
3. De-hiding of specs (`*_spec.spl` public copies from `.spipe_matchers_*`) must follow the spipe harness convention — check how other clusters expose specs before copying.
4. Verify `text.from_char_code` availability in interpreter mode for the text-wrapping functions in utf8.
