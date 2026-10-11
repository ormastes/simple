# PureDatabase treats total numeric conversions as optional parsers

Status: OPEN — source repair and executable regressions authored; native and
SSpec execution UNEXECUTED.

## Actual failure

The b58 Phase4 PostgreSQL build with producer `892b220e19b5cbafd620190c95b9a2f26fc5ebc08304b8b07d4475da0ea7abb0`
reported four unresolved `is_none`/`unwrap` methods at row_value_helpers lines
293/297 and two `DbValue.Real` payload mismatches at lines 251/326. Retained
artifact: `postgres-text-numeric-conversion-contract-audit.json` under the
2026-10-11 phase2 CUDA-owner evidence directory. The corresponding release
226d caller file is byte-identical to that failed source.

`to_int` and `to_float` return plain numbers. They are total conversions;
`parse_int` and `parse_f64` preserve failure as an optional result. MIR,
owned runtime implementations, and `probe_parse_family_option_jit.spl`
agree on this distinction. Numeric validation must not call Option methods
or match `Some` on a total conversion. The row-length parser had the same
mistake even though the current error list did not isolate that site.

## Scoped repair

Use `parse_int` for checked cell lengths and canonical integer validation,
and `parse_f64` for v2 Real rejection and canonical Real validation. This
preserves integer overflow detection and separates valid numeric zero from
invalid text. Keep the existing total conversions in legacy v1 decoding,
v2's already spelling-checked integer conversion, SQL literals and integer
expressions; remove their inapplicable `?? 0`/`?? 0.0` operations. No numeric
conversion builtin or runtime API changes.

Native integer conversion currently retains leading-prefix/clamping semantics;
the owned interpreter has different malformed-input details. This change does
not normalize those pre-existing differences or promise NaN/Inf policy changes.

## Prevention and qualification

- `test/01_unit/lib/database/pure_database_numeric_parse_contract_spec.spl`:
  six public-contract cases. Real framed v2 open/scan and v3 checkpoint/reopen
  preserve integer zero, three, negative numbers, real zero and finite fractions.
  Valid-checksum malformed, truncated, empty, overflowing-length, noncanonical
  and overflowing-integer rows are rejected without changing persisted bytes.
  A corrupt checksum is rejected. Legacy numeric defaults and SQL literals
  remain usable; total and fallible conversion families stay distinct.
- `test/fixtures/compiler/pure_database_numeric_parse_contract/main.spl`:
  native public API reproduction/prevention with nonzero failure exits, framed
  persistence, roundtrip values, malformed input and legacy SQL insertion.

Neither fixture imports private row helpers or replaces the actual persistence
path with an isolated copy. Tests must use the source-bound pure-Simple compiler
and natural runtime link. Static checks are not execution evidence. Independent
DbValue owner, method, slice and enum-payload failures may still block this full
closure; this repair does not claim all PostgreSQL errors are resolved.
