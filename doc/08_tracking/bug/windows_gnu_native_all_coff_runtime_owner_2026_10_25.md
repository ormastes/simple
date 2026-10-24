# Windows GNU native-all skips the COFF runtime owner composition

Status: first-miss functional Windows GNU projection and strict native probe
**PASS** on native attempt 3, source round 4 (maximum six). The independent
packed-byte limit repair landed as PR4489 before the passing attempt. Fast cache,
self-hosted, full compiler and Phase3/4 qualification remain pending.

Actual candidate `2cc51dc392b19a3f2fceffcac2d42d0b54fd32caf87eea7c69302656633ac7a7`
compiled Hello through native object generation, then strict linking failed on
duplicate definitions in loose `runtime.o` and `runtime_native.o`. Evidence is
retained under `C:/dev/simple-gnu-linkfix-hello-20261025`, especially
`evidence/hello-failure.sdn`, its compile receipt/log and generated link command
SHA256 `9d4f24cb3c0d27b7c49f797ef4a3ea8b43b8eb2b69bf3b6530bbedf55c05c85c`.
Native/raw exit 1, jobs 24, peak RSS 239,932 KiB, quiescent 1; Hello was not run.
The first error proves conflicting C inputs, not archive overlap.

The orchestrator excluded `_is_mingw()` from `coff_native_all`. Native-all then
prevented the ordinary-to-core-C fallback, leaving both monolithic runtime.c
and runtime_native.c. The existing owner-c core-C selection and archive ceding
only ran for MSVC. Flipping that condition alone is invalid: the existing
MSVC archive helper requires and seals `LLVM-C.lib`, absent from the actual GNU
authority, and emits the MSVC archive basename.

The repair keeps the existing MSVC helper unchanged and adds a separate GNU
adapter. Explicit Windows target ABI takes precedence over host/ambient driver;
native default targets are normalized from actual host architecture and MinGW
selection. GNU/gnullvm AMD64 and ARM64 projections validate every C object and
recognized COFF/archive import member against the expected machine. The shared
parser keeps the exact existing two-argument native entry point. A separately
named three-argument entry point validates the expected machine for GNU; cached
two-argument callers never acquire an argument-count mismatch.

GNU output is `libsimple_native_all.a`, with no fabricated MSVC library.
Content identity binds the resolved target, expected machine, ABI v1, source
archive full hash and ordered C object full hashes. Paths are separately
validated but excluded from compatibility keys, so PID-based temporary object
names do not invalidate byte-identical inputs. Cache integrity is
checked against projection bytes recomputed from those real inputs, not a
receipt-selected output hash. Strict managed callers still require a pre-ceded
archive. No duplicate-forgiveness switch, stub provider or Rust rebuild is added.

The existing ar/member/index-preserving ceder is reused. Its precondition stays
mandatory: loose C objects precede the projected archive, because the original
ar index still names ceded symbols. GNU system/runtime dependencies remain with
the existing driver and original authority; this local projection is not a new
runtime admission or companion-fingerprint authority.

## Fast cache acceptance remains pending

The current functional implementation recomputes the source-rooted projection
before accepting a cached result. This rejects tampering of both output and
its local receipt, but is O(archive bytes) and is **not a fast cache lookup**.
First-miss functional qualification is separate. The functional fix lands with
the performance limitation recorded in
`gnu_coff_projection_fast_cache_pending_2026_10_25.md`; no fast-cache acceptance
is claimed. No unchanged passing check may be repeated to hide this missing gate.

A future fast path needs either a trusted writer-owned immutable projection
witness within an admitted runtime authority, binding the stable input key to
the expected output digest, or efficient structural validation rooted in the
original archive. Ordinary local SDN plus its own output hash is not that
authority. Existing MSVC size-only cache behavior is not reused as a GNU proof.

## Actual retained first-miss evidence

Root: `C:/dev/simple-gnu-coff-owner-storage-20261025`. Original `projection` and
`diagnostic2/projection` failed with native DWORD `0xC0000409`/collector 125 on
the retained assertion. Diagnostic2 proved all 24 target cases, real input paths,
28 objects and DC022 hash before reporting the archive-read refusal. The real
109,939,334-byte archive exceeded the old packed-array limit of 100,000,000;
these failures and their original helper binaries/logs remain preserved.

`diagnostic3` used release `6e2b560dab60a5d8e379f593fe4f6dd635a7da97` plus this
three-file owner patch, actual byte-capacity-fixed canonical C objects, and the
same immutable bootstrap seed 5a6a. This is a bootstrap diagnostic, not a
self-hosted test. No Rust seed or compiler generation was rebuilt.

- Helper build: native/raw 0, 1 fresh/55 reused units, 5.4s; real core-C source
  contains the landed byte-capacity repair. Projection: native/raw 0, all 24
  target cases, actual DC022/28-object input, peak 404,356 KiB.
- Selected projection SHA256:
  `6923460be7a185e135ca81c2a6d203e8a56f2a497990e0e45228797e47025537`.
  Original archive and all frozen input pins were unchanged.
- `original-negative-link`: real strict Clang/LLD exit 1 specifically for C vs
  archive duplicate owners (`max`, `panic`, `rt_cli_run_file`, and others), with
  no missing-library oracle accepted.
- `derived-positive-link`: native/raw 0, no duplicate/unresolved allowance or
  fabricated provider. `derived-positive-run`: native/raw 0 and exact output
  `gnu-coff-native-owner rust_signature_calls=24 aliases=2 boxed_owner=c`.
  This executes real Rust Cranelift code and retained thread alias bodies.
- `preservation-proof`: native/raw 0; all 2,907 archive member headers/offsets
  unchanged, both metadata/index/long-name members byte-identical, and all
  89,318 non-C-owned definitions preserved. `rt_native_build`, Cranelift signature
  and both thread aliases each retain exactly one archive definition. Detailed
  ledgers/result are under `diagnostic3/preservation-result`.

All five functional stages and preservation verification retained the real
Windows Job collector, independent 5,859,375-KiB RSS guard, 24 requested workers,
raw status and quiescent 1 receipts. No passing native control was repeated.
Unit-spec mismatch/refusal tests remain authored rather than claimed executed;
the full 39-C-object profile, default compiler Hello and fast-hit/tamper gates
remain separate pending acceptance.

Managed strict ceding still rejects on-the-fly changes. The earlier 2cc Hello's
retained clean environment supplied no managed tool authority selectors, so
`SIMPLE_BOOTSTRAP=1` alone did not make that diagnostic strict. A canonical
managed descendant needs an explicitly frozen pre-ceded authority matching its
actual C composition and original runtime companion lineage. Never replace
DC022 beneath its receipt or disable strict admission to make that stage pass.
