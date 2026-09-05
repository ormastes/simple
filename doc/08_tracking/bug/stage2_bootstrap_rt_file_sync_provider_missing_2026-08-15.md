# Stage 2 bootstrap link lacks the C-only `rt_file_sync` provider

**Status:** root fix implemented and focused Rust regression passed; canonical
verification is blocked before Stage 2 by the authority-fingerprint bug.
**Observed:** 2026-08-15.

## Canonical failure

The manifest-verified canonical transaction used corrected seed SHA-256
`3d7d1c59ba5bb3e7c27bd8758b284d7b6fc02559c997f2e3e4b790f776e9b7fe`
and reached Stage-2 link. It compiled 846 entry-closure modules (0 cached) and
then exited 1 on four unresolved references to `rt_file_sync`:

- `mod_568.o`: two calls from `driver_native_publish_object`;
- `mod_582.o`: two calls from `BuildCache.save`.

Retained evidence:

- immutable copy
  `build/native_probe/stage4-owner-20260815/stage2-native-build-rt-file-sync-failure.log`
  (SHA-256 `e2b3c56e05eee8af34d027c9a544a764267d27c02f6fa9c51ad8b0a0b7b6ab5c`);
- `build/bootstrap/stage3/x86_64-unknown-linux-gnu/native-objects-ut9biT/`;
- `build/native_probe/stage4-owner-20260815/canonical-after-classinstance-callable-runtime-fixes.{log,status,time}`.

The transaction inventory was 13,016 inputs and 12,410 Simple files: 1,749
compiler, 7,821 library, and 2,616 application files. Whole-transaction time
was 17m04.22s with 2,698,352 KiB peak RSS. No Stage-2 candidate, hash, sanity,
receiver receipt, Stage 3, or Stage 4 was produced.

## Root cause and fix

The canonical bootstrap-main link selects `libsimple_native_all.a` plus a
localized core-C supplement. Native-all owns compiler/native-build providers
but does not contain the C-only `rt_file_sync` implementation from
`runtime_legacy_core.c`. The core-C authority archive defines the symbol, but
`build_bootstrap_mutex_runtime_capsule_archive` projected only five mutex
exports, so the final link had no admitted `rt_file_sync` owner.

`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs` now adds only
`rt_file_sync` to that localized bootstrap core ABI. The existing exact-export
test in `native_project/tests.rs` now requires the five mutex exports plus
`rt_file_sync`, while continuing to reject unrelated runtime/compiler exports.
No stub, fallback, Simple caller rewrite, or whole-archive relaxation is used.

Focused test (1 passed, 0 failed):
`pipeline::native_project::tests::test_bootstrap_mutex_capsule_exports_only_canonical_core_abi`.
Log:
`build/native_probe/stage4-owner-20260815/rt-file-sync-bootstrap-capsule-focused.log`.

## Bounded next gate

The first pre-retry guard correctly refused to launch: published seed SHA-256
`3d7d1c59ba5bb3e7c27bd8758b284d7b6fc02559c997f2e3e4b790f776e9b7fe`
was published at 04:40 UTC, before the 04:49 capsule fix. Manifest SHA-256
`cdb15cf755ee14ba561d6dede841ba077a848a6fca9e5ef46863beb456dc5586`
also failed its precheck on five changed covered files and does not list the
new provider-symbol gate. Evidence:
`build/native_probe/stage4-owner-20260815/pre-retry-manifest-stale.log`.
No Stage-2 process was started from this rejected state.

The reviewed manifest was ultimately refreshed to SHA-256
`6c041d7a4378b9ec3be2b57a348ab55bd4d73d11192a71741ed95a0c7a57b2a0`
with 27,071/27,071 listed files verified. The corrected authority build then
hit the distinct self-generated fingerprint drift recorded in
`stage2_rust_authority_fingerprint_includes_generated_build_outputs_2026-08-15.md`
before publication or Stage 2. After that root is fixed in a fresh bounded
session, run one Phase-2-only transaction with the preserved cache:

```sh
SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --bootstrap-receipt=build/native_probe/stage4-owner-20260815/reason-stage2.receipt \
  --full-bootstrap --stop-after-stage2
```

Success requires the admitted Stage-2 binary, exact candidate hash, sanity and
struct-receiver receipts, and no Stage-3/Stage-4 start. A distinct first
failure is retained and fixed only within the remaining bounded cycle budget.
