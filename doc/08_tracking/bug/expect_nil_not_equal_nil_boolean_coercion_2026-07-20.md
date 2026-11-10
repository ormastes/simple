# `expect(nil != nil)` yields nil instead of boolean false (only when both sides are nil)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** CLOSED 2026-11-11 — FIXED on release; verified by lane ne8 (seed 46fe8f6b6def)
**Found:** 2026-07-20 (whole-suite triage campaign, test/01_unit shard)
**Area:** interpreter — `!=` operator / SSpec `expect()` boolean coercion

## Note: recommended fix is NOT applied to the file (leaves 1 residual failure)

`test/01_unit/lib/ffi/ffi_signature_spec.spl` currently fails 2 of 7
examples via the known, already-filed `.?` identity-passthrough bug
pattern: `expect(sig.?).to_equal(true/false)`. The obvious migration is
`expect(sig.?)` -> `expect(sig != nil)` (value-preserving, per this
campaign's documented pattern). Trying that locally: the "retrieves by
name" case (`sig` non-nil, expects `true`) goes green, but the "returns nil
for unknown name" case (`sig` IS nil, expects `false`) trades its original
failure for a **different, genuine** failure (below) rather than passing —
so the spec still can't reach green either way. Per this campaign's rule
(leave GENUINE-BUG specs unmodified, file a doc instead of carrying a
partial edit), **the `.?` -> `!= nil` migration was NOT kept in the
file** — do that migration first when someone follows up on the failure
documented here.

## Symptom

With the `.?` -> `!= nil` migration applied locally for `sig`:

```
it "returns nil for unknown name":
    var m = FfiManifest.create()
    m.add("T32_Ping", 0, "i32")
    val sig = m.get("T32_NonExistent")   # FfiManifest.get() -> FfiSignature? ; returns literal nil here
    expect(sig != nil).to_equal(false)
```

Fails with:

```
✗ returns nil for unknown name
    expected nil to not equal nil
```

(Against the current, unedited file this same underlying case instead
shows the original `.?`-passthrough symptom: `expect(sig.?).to_equal(false)`
-> `expected nil to equal false`. Both are the same root defect area — nil
handling in comparisons/coercions — but the `!= nil` form surfaces the more
precise "nil doesn't coerce to boolean false" defect described below.)

`sig` is genuinely `nil` here (`FfiManifest.get(name: text) -> FfiSignature?`
in `src/lib/nogc_sync_mut/sffi/sffi_signature.spl:31-34` falls through to
`nil` when the entry isn't found). So `sig != nil` is `nil != nil`, which
should evaluate to boolean `false`. Instead it appears to evaluate to `nil`
(untyped/unboxed), which then fails `.to_equal(false)` with the confusing
message "expected nil to not equal nil" (the message itself looks like it
comes from a different/negated matcher path than a plain boolean equality
check, suggesting the `!=` comparison result isn't a clean `bool` by the
time it reaches `.to_equal()`).

The sibling case one line above it (`sig` genuinely non-nil,
`expect(sig != nil).to_equal(true)`) passes fine — the defect is specific
to the `nil != nil` (both-sides-nil) case.

## Root-cause hypothesis

Consistent with this codebase's known nil/Option-handling interpreter
quirks (see project reference notes on `.?` returning non-boolean and
general nil-comparison landmines): the `!=` operator's result, when both
operands are `nil`, does not get coerced to a proper `bool` (`false`) the
way a nil-vs-non-nil comparison does — it appears to propagate `nil`
itself as the comparison's "falsy" result instead of `false`, and that
raw `nil` then fails an explicit `.to_equal(false)` check (nil != false
by strict equality) rather than being treated as boolean false.

## Minimal repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/lib/ffi/ffi_signature_spec.spl --no-session-daemon
```

## Affected specs seen this shard

- `test/01_unit/lib/ffi/ffi_signature_spec.spl` — 2 examples currently fail
  via the known `.?` bug (not fixed in-file, see note above); "returns nil
  for unknown name" specifically will still fail with this doc's distinct
  `nil != nil` defect even after the `.?` -> `!= nil` migration is applied.


---

## 2026-11-11 addendum — lane ne8 (P3 traverse, batch ne8)

**Verdict: FIXED on release — the `nil != nil` form now coerces to boolean false.**

- **Direct probe (seed-smoke, seed 46fe8f6b6def):** a spec asserting
  `expect(nil != nil).to_equal(false)`, `expect(nil == nil).to_equal(true)`, and a
  non-nil `!= nil` control — **3/3 examples PASS** (`simple test --mode=interpreter --no-cache`,
  probe under `build/review/`). The both-sides-nil case no longer propagates raw nil into the
  matcher.
- **Affected spec re-run (seed-smoke):** `test/01_unit/lib/ffi/ffi_signature_spec.spl` —
  **7/7 PASS**, including "returns nil for unknown name" (`FfiManifest.get` falls through to nil;
  `expect(sig.?).to_equal(false)` now yields the genuine boolean). The spec file was never
  migrated to `!= nil`; the seed interpreter's nil/`.?` comparison handling was fixed underneath
  it.
- **Related fix:** `5a06a70c8b74` `fix(seed-bdd): keep .? as T? when compared with nil in
  expect; close stale .? rows` (2026-11-05, on release tip), which closed the sibling
  `.?`-passthrough rows (`optional_query_operator_identity_passthrough_2026-07-20`,
  `option_predicate_returns_payload_not_bool_2026-07-28`, ...). This row's distinct
  both-sides-nil symptom also no longer reproduces.
- The recommended `.?` -> `!= nil` migration is therefore no longer required to reach green;
  both spellings now pass.
