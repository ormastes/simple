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

## Performance and memory intent

The compiler may allocate during compilation, but closure discovery must remain
linear in admitted source bytes plus import edges, avoid value-copy insertion,
and remain within explicit source/import cardinality limits. No retry loop may
hide a failing preflight or trade lower wall time for unbounded RSS.
