# Compiler entry-closure build CPU/RSS regression (2026-08-22)

## Status

Open — source fixes exist, but a source-matched Pure-Simple measurement is pending.

## Evidence

The retained MC/DC source-matched recovery receipts show two non-converging full
build attempts:

- `build/native_probe/mcdc_source_matched/result.env`: 1071.71 s and
  1,478,536 KiB maximum RSS.
- `build/native_probe/mcdc_source_matched/result_cycle2.env`: 1099.69 s and
  1,399,268 KiB maximum RSS, ending with 29 failed files.
- The focused core closure took 286.5 s and 208,444 KiB, versus 13.7 s for the
  focused HIR codec and 5.16 s for Trace32.
- Current-tip cycle 3 (`ebb960009aeb`) used the preserved cache and native
  arenas, produced 1,886 additional cached objects, but still failed after
  945.43 s with 1,576,520 KiB maximum RSS. This is 11.2% faster than the
  1071.71 s baseline but 6.6% higher peak RSS than 1,478,536 KiB, so the
  performance/memory acceptance criterion remains failed.
- Cycle 4, after failed-shard fixes, reached 8,000 cached objects but still
  produced no candidate: 865.15 s and 1,447,228 KiB maximum RSS. Wall time is
  19.3% below the original 1071.71 s baseline and peak RSS is 2.1% lower than
  1,478,536 KiB, but both remain excessive and correctness is still blocked.
- Cycle 5 was the third and final full attempt for the scoped recovery session.
  It reached about 10,000 cached objects but produced no candidate after
  1234.90 s and 1,478,060 KiB maximum RSS. Five files remained: the old
  admitted builder still enforced its embedded 60-second limit on frontend
  core and generated HIR codec; one SMF executable-memory body, one browser
  color body, and one legacy complex indexed lvalue also remained. The hard
  three-cycle cap prohibits another full retry in this session.
- The two Cycle 5 timeouts were an invocation defect, not evidence that either
  unit exceeded every bounded budget.  The admitted builder embeds a 60-second
  per-file default and advertises `--timeout <secs>`; the Cycle 5 command omitted
  that option.  One isolated-cache focused probe per affected unit with
  `--timeout 600` crossed the old boundary and reached linking without a timeout
  or failed-file verdict:
  - frontend core: 226.63 s, 203,768 KiB maximum RSS;
  - generated HIR codec: 34.06 s, 178,772 KiB maximum RSS.
  Receipts are retained under `build/native_probe/mcdc_timeout_fix/`.  Both
  focused link steps then failed on missing runtime symbols, which is outside
  the per-unit compiler-timeout category.  The next cache-preserving recovery
  invocation must pass `--timeout 600`; this remains fail-closed at ten minutes
  per unit and must not be replaced with an unbounded timeout.
- A focused Rust compiler regression-test build for array-lvalue lowering was
  blocked before test execution by the unrelated missing
  `crate::interpreter::dispatch_profile` owner after 99.41 s and 2,164,056 KiB
  maximum RSS. Test-build dependency closure and RSS therefore require their
  own reduction; this run is not correctness evidence for the lowering fix.

Static profiling identified value-semantic `Dict` copies in
`_driver_text_bucket_set_add`, unbounded source splitting, and globally keyed
relative-import deduplication. Commits `741329cc966f` and `8a08bc5f95b2` remove
the copy helper, add fail-closed scan bounds, and scope relative imports by
declaring directory. These are not performance proof until measured with an
admitted source-matched compiler.

## Required acceptance evidence

1. Run the closure-focused preflight before any full build and fail within
   15 seconds for unresolved `ffi`, `raw_ptr`, or scoped unsafe ownership.
2. Retain wall time, maximum RSS, source count, import count, cache identity,
   compiler/source identity, and failure category counts.
3. Demonstrate that direct indexed set mutation is used on every closure hot
   path and that source/import/physical-source caps fail closed.
4. A successful build is not sufficient: compare against the retained
   1071.71 s / 1,478,536 KiB baseline and investigate any regression.
5. Do not deploy unless the candidate passes the four-word environment ABI
   admission probe and contains no code-generation stub fallback.
6. When the admitted builder is used, pass `--timeout 600` explicitly and retain
   per-unit timeout verdicts.  Its embedded 60-second default is below the
   measured 226.63-second frontend-core cost; omitting the option recreates a
   known false timeout rather than a meaningful performance gate.

## Performance and memory intent

The compiler may allocate during compilation, but closure discovery must remain
linear in admitted source bytes plus import edges, avoid value-copy insertion,
and remain within explicit source/import cardinality limits. No retry loop may
hide a failing preflight or trade lower wall time for unbounded RSS.
