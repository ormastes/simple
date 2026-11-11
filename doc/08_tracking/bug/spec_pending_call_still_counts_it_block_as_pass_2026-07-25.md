# `pending(...)` inside an `it` block is counted and reported as a PASS

- **Date:** 2026-07-25
- **Area:** test runner / `std.spec` pending reporting
- **Severity:** high — this is a **false-green** mechanism. Every spec that
  parks work behind `pending("...")` currently inflates the passed count.
- **Status:** FIXED 2026-11-11 — verified fixed on release tip: pending()
  now marks the example pending (skipped), excluded from passed. See the dated
  addendum at the end of this file.

## Symptom

`pending("reason")` prints its own yellow `○ reason (skipped)` line, but the
enclosing `it` block still prints `✓` and is still tallied as a **passed**
example. Nothing is subtracted from the total and nothing is reported as
pending in the summary.

Reproduced while un-parking
`src/lib/gc_async_mut/pure/test/tensor_spec.spl`:

```
bin/simple test src/lib/gc_async_mut/pure/test/tensor_spec.spl
```

```
  String Representation
    ✓ shows the shape
    ○ f64_integral_to_text_drops_fraction_2026-07-25 (skipped)
    ✓ shows 1D tensor elements
    ○ f64_integral_to_text_drops_fraction_2026-07-25 (skipped)
    ✓ shows 2D tensor elements
  Static constructors on the generic class
    ○ generic_static_method_type_param_unresolved_2026-07-25 (skipped)
    ✓ PureTensor.from_data

30 examples, 0 failures
...
Results: 30 total, 30 passed, 0 failed
```

`PureTensor.from_data` asserts nothing at all — its body is a single
`pending(...)` call — yet it is reported as a passing example.

## Why it matters

`pending()` was clearly intended to be the honest way to park a test. As
implemented it is indistinguishable from a green test in the authoritative
`Results:` line, which `.claude/rules/testing.md` designates as the sole
verdict. So parked work reads as delivered work.

Existing specs affected (all currently contribute PASSES for tests that assert
nothing):

- `test/01_unit/lib/crypto/bcrypt_kat_spec.spl:189,194`
- `test/01_unit/lib/crypto/argon2id_rfc9106_kat_spec.spl:134`
- `test/01_unit/os/crypto/argon2d_kat_spec.spl:138`
- `test/01_unit/compiler/r2_pending_helper_spec.spl:34`
- `test/03_system/compiler/rtl_mdsoc_byte_equal_spec.spl` (7 sites)
- `test/03_system/compiler/debug_sidecar_json_order_spec.spl` (9 sites)
- `test/05_perf/**` bench specs (6 sites)
- plus the mirrored `test/unit/**`, `test/system/**` copies of the above

## Expected

`pending()` should mark the enclosing example pending: excluded from the passed
count and surfaced in the summary line, e.g.
`Results: 30 total, 27 passed, 0 failed, 3 pending`.

`src/lib/nogc_sync_mut/spec.spl:186` already increments a `test_pending`
counter, but the runner path used by `bin/simple test` does not consume it and
`_execute_it` marks the example passed regardless.

## Not fixed here

Fixing this changes the reported totals of the whole suite, so it needs to be
done deliberately rather than as a side effect of un-parking one spec.

---

## Addendum 2026-11-11 — lane runner7: FIXED verified on release tip

Reproduced the filing shape on the refreshed Windows seed (`bin/simple.exe` at
HEAD `68ab3383080f`, 2026-11-11) with a 3-example probe (real assert,
`pending("parked_reason_2026-11-11")`, real assert):

```
○ parks work (pending)
SPEC FILE VERDICT: ... outcome=OK declared>=3 executed=3 passed=2 failed=0 skipped=1 dropped=0
Results: 2 total, 2 passed, 0 failed
```

The pending example no longer inflates the passed count — it is tallied as
`skipped=1` and excluded from `Results: ... passed`. The mechanism this doc's
"Expected" section asked for is implemented in `src/lib/nogc_sync_mut/spec.spl`:
`_execute_it` snapshots `test_pending` before the example (:395) and, when the
counter advanced, emits the `finished/pending` trace event and returns
`"pending"` instead of marking the example passed (:425-430).

Regression evidence (the doc's own named affected spec, no edit needed):
`bin/simple.exe test test/01_unit/compiler/r2_pending_helper_spec.spl --mode=interpreter --no-cache`
-> `outcome=OK declared>=2 executed=2 passed=1 failed=0 skipped=1`,
`Results: 1 total, 1 passed, 0 failed`, rc=0.

Verdict: FIXED — absorbed by the std.spec pending-consumption fix; no lane
code change needed beyond this status flip. (The summary line renders pending
as `skipped` rather than a separate `M pending` token; the false-green
mechanism — the subject of this record — is closed either way.)
