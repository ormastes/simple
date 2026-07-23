# Native `text?` map falls through to `str.map`

**Status: resolved on 2026-07-23.**

## Reproduction

Before the fix, `scripts/check/check-native-flat-option-map.shs` passed integer
and float optional mapping plus all evaluation-count checks, then exited `51`:

```text
Simple runtime error: function not found: str.map
```

Both the same-module `next_text() -> text?` row and an imported provider row
remain in `test/fixtures/native_flat_option_map/`; do not delete or weaken them.

## Evidence

- Root cause: non-bootstrap `native-build` rewrote every `text?` token to
  `text` before parsing. Bootstrap compatibility rewriting remains unchanged;
  normal native parsing now preserves source exactly.
- Focused source-selection regression: passed 1/1.
- Typed flat-Option MIR regression: passed 1/1.
- `scripts/check/check-native-flat-option-map.shs`: passed against verified
  self-hosted Stage3.
- Final refreshed Stage2 SHA-256:
  `42391ee607aa8e243d9222afc1021e1f03f426c5701ea17591d63f4037662f78`.
- Final refreshed Stage3 SHA-256:
  `8641e1d637db3c8012a2b1a8b203f67f99ecce45a3c884cb8ed6cd9c1906aae8`.
- The wider cross-module fixture advanced from exit `6` through the Option
  receiver-count assertion to exit `7`, its independent nested-copy row.

## Rejected hypotheses

Recording declared function returns in HIR under local/import-alias names did
not change the executable result, whether stored directly or through the
existing one-element-array cross-pass carrier. Those ineffective changes were
removed.

## Related correction

The cross-module receiver counter used an unannotated integer module `var`,
which the HIR declaration pass typed as `Any`. Native code stored raw `1` but
dynamic equality compared it with boxed `1`. Bare integer-literal module vars
now infer `i64`; the focused declaration/init/store regression passed and
higher review accepted the narrow fix. The remaining exit `7` must be handled
in a fresh bounded nested-copy lane before Stage4.
