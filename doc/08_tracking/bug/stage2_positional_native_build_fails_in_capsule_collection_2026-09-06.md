# Stage-2 positional native-build fails in the capsule-collection checkpoint, silently

- **Date:** 2026-09-06
- **Status:** OPEN (diagnostics landed; producer defect not yet fixed)
- **Severity:** release-blocking — sole blocker to a completed bootstrap
- **Area:** `src/compiler/80.driver/driver_aot_native_output.spl`, native AOT collect lane
- **Host:** aarch64-unknown-linux-gnu
- **Subject binary:** `build/bootstrap/stage2/aarch64-unknown-linux-gnu/simple.rejected`

## Symptom

Stage-2 sanity builds `scripts/check/cert/redeploy_gate/fixtures/hello_world.spl`
in **positional** form and fails with zero errors at every lowering checkpoint
and no diagnostic at all:

```
[bootstrap-error-count] point=entry|post-lowering|post-diagnostics|post-store   count=0
ERROR: 1 unit(s)
  reason: (none recorded — BUG in the producer: a non-OK unit must carry a diagnostic)
```

Reproduced twice here, `--backend llvm`, rc=1.

## What was actually established

**The AOT compile SUCCEEDS. The build fails afterwards, in collection.**

Both runs leave, in the cache scope directory:

| artifact | state |
|---|---|
| `object.scripts.check.cert.redeploy_gate.fixtures.hello_world.o` | present, **1080 bytes** |
| `…o.capsule-receipt` | present, 1278 bytes |
| `build_cache.sdn` | `entries: []` — empty |

The object and its receipt are both written by `_compile_frozen_module_capsule`
*before* it returns `Ok`. `build_cache.update_entry` is reached only *after*
`driver_native_collect_capsule_result_v1` succeeds. Object present + receipt
present + cache empty pins the failure to the collection checkpoint.

This **refutes** the natural reading of the earlier record
`stage2_aot_error_message_lost_invalid_heap_2026-09-06.md` as the whole story for
this failure: `_aot_compile_failure` — the only raising site in this file that
prints — was not on the failing path. The log contains no
`error: AOT compile error in …` line because that code never ran.

**Why nothing was printed.** `driver_native_collect_capsule_result_v1` was the
one failure path in the file that never printed, and communicated its reason only
by returning a bare tag. That tag arrived at `BuildOutcomeSet` empty, and the
summary rendered it as "(none recorded)". Two further amplifiers:

- the summary's two "(none recorded)" fallbacks emitted **byte-identical** text,
  so "stored nothing" and "stored something that renders as nothing" — different
  defects, different fixes — were indistinguishable;
- all four collect reasons are interpolated (`"native-capsule-…:{module_name}"`),
  so a corrupt operand can silence the literal text around it.

**Fingerprint anomaly (measured, cause not proven).** The receipt records the
object's fingerprint as:

```
size          = 16        (the object on disk is 1080 bytes)
content_hash  = 241       (not a sha256; `rt_hash_text` returns an i64)
```

identical across both runs. `FileFingerprint.from_file`
(`driver_build/incremental.spl:350`) intends to fall back to
`rt_file_hash_sha256` for binary files, on the assumption that
`incremental_file_read_text` returns nil for non-UTF-8 content. The measured
values are **consistent with** that assumption being false — a short text
returned at the ELF header's first NUL run (`\x7fELF\x02\x01\x01\x00` + NUL
padding through offset 15) — but that has not been proven, and `size` comes from
a separate `rt_file_size` call which should not be affected by it.

**Not yet explained:** whether the receipt check is the failing sub-check, and if
so why, given that write-time and validate-time fingerprints come from the same
function. A value stable across RUNS need not be stable across CALLS within one
run; the receipt is written by one `FileFingerprint.from_file` call and validated
by another. The `expected-len` / `actual-len` pair added below is what settles it.

**Also unexplained:** the log carries exactly one blank line per failure,
immediately before each build-outcome summary, from an unidentified print site.

## What landed (diagnostics only — the producer defect is NOT fixed)

- `driver_native_capsule_result_invalid_reason_v1` — the receipt check had five
  independent ways to return `false`, all collapsed into one tag. Now returns the
  sub-check plus its measured values; the bool version delegates.
- `_collect_failure` — prints at the raising site: a pure-literal line first
  (no operands, so nothing can silence it), then module / tag / detail **bare**
  (no interpolated temporary), then the lengths.
- `_aot_compile_failure` — same three-part robust shape, for the other raising site.
- `driver_native_nonempty_failure_detail` — also tests `.len()`, because `!= ""`
  does not reject a corrupt tagged word.
- `BuildOutcomeSet.reason_block_for` — the two fallbacks now name their site
  (`[empty-at-record]` / `[lost-in-render]`) and report the measured length.

## Fence

`scripts/check/check-aot-failure-speaks.shs --candidate <binary>` — a failed
native-build unit must state why. About attributability, not success: a build
that succeeds passes; a build that fails passes only if it named a reason.
Fatal 5-fixture selftest. Scope limit: positional form, `--backend llvm` only.

## Next step

Rebuild a Stage 2 carrying these diagnostics and read the
`native-capsule-*` line it now prints. That names the failing sub-check without
guessing, which is the point — every hypothesis above that is not marked
MEASURED is a hypothesis.
