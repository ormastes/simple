# `protocol.json_int_field` fails on the release seed: `text.ord()` not found

- **ID:** slang_protocol_json_int_field_text_ord_missing_release_seed_2026-11-20
- **Status:** OPEN (worked around in `serving_pooling.spl`)
- **Seed:** `C:/dev/seeds/simple-release.exe` (interpreter lane), Windows

## Symptom

`json_int_field` in
`src/lib/gc_async_mut/slang/entrypoints/openai/protocol.spl` computes each
digit as `ch.ord() - "0".ord()`. On the release seed the first call aborts the
request with `Runtime error: Function 'ord' not found`
(`/v1/rerank` with `"top_n": 2`, 2026-11-19; log
`C:/dev/slang-logs/l4/serve.log`).

## Scope

Every caller of `json_int_field` on that seed (`max_tokens`, `top_n`, ...).
Distinct from `native_text_ord_missing_lowering_2026-10-10.md`, which is the
native-codegen lane.

## Workaround

`serving_pooling.spl` reads `top_n` from the parsed JSON tree
(`json_parse_with_error` + `json_object_get`, value type `number`). The fix
belongs in `protocol.spl` (or in the seed's `text` method table).
