# Rust bootstrap runtime omits the secure-temp split ABI

Status: Windows native-all and canonical full-C adapter regressions **PASS**.
Source-fix round 1, native verification cycle 5 of maximum six (including a
launcher failure before compilation). This is not compiler, Hello, Phase 2,
POSIX, or full-runtime qualification.

The retained `eadb47f7722b0081c16dd87d0b057c3cba0c2cbd` seed
`5a6a8bec8c8c205b2c4507768acf553b3ef6027018706357350394af09f81622`
reused 1,350 objects and compiled 138. Its linked candidate contained generated
unresolved-symbol stubs. The candidate's real Hello compilation exited 1 at
`snapshot-staging-create-failed`, before HIR/object generation. The selected
runtime archive was `9cf7ec1d154a22a475cabd4cc8d632d7488daf1e488a0f7f821ace6109e7d6f7`.
Retained evidence lives under `C:/dev/simple-gnu-warm-storage-20261024/attempt2`
and `C:/dev/simple-gnu-runtime-storage-20261024/evidence`; these artifacts remain
unchanged.

`file_ops.secure_temp_dir_raw` calls the two boxed-text setters, requires each
to return exactly 1, then invokes zero-argument `make`. Those three names were
absent from the archive and appeared in the generated-stub inventory. The real
four-argument `rt_secure_temp_dir` was already present: Cargo compiles
`runtime_secure_staging.c`, while the three split adapters existed only in
`runtime_native.c`. Including that entire translation unit would duplicate
Rust-owned runtime exports.

The repair shares only the boxed-text adapter in
`runtime_secure_temp_split_private.h`, included by the mutually exclusive full-C
and narrow Rust-bootstrap providers. It delegates creation to each provider's
existing real OS function. No feature macro, Rust owner, stdlib declaration,
source/cache key, or snapshot admission rule changes. Cargo's existing recursive
`../../runtime` watch covers the new header.

The adapters preserve 4,096-byte parent/128-byte prefix bounds, thread-local
slots, single boxed arguments, and consumption of both slots before every OS
attempt. Two intentional fail-closed corrections apply to both C owners:
embedded NUL text is rejected instead of truncated, and a failed setter clears
its ready flag so an earlier successful value cannot be reused. Raw string
literal pointers remain supported by the full-C text owner; arbitrary invalid
pointer words are not claimed safe or used as tests.

## Review before execution

The native fixture is
`src/runtime/test/rt_secure_temp_split_native_all_selfcheck.c`. It must link
against the newly built real Rust `libsimple_native_all.a`; it defines no fake
runtime functions. Its inputs/outputs cross actual `rt_string_new`,
`rt_string_len`, and `rt_string_data`. It checks missing/empty/oversized/NUL
inputs, separator rejection, valid-to-invalid setter replacement, consumption
on missing pair/OS failure/success, exclusive distinct children, real Unicode
directories beyond MAX_PATH, protected SYSTEM/owner-rights ACLs, and 24
interleaved OS threads with different parents and prefixes. It validates real
directories and removes only its inventoried children in reverse order.

After root review, use one new private runtime target/output/cache, the exact
eadb source plus this patch, the retained GNU toolchain and normal 6-GB resource
guard, `cargo build --profile bootstrap -p simple-native-all --features
driver-compat --jobs 24`. Do not rebuild the seed or modify the old archive.
Retain complete input/tool/source/runtime hashes and final status.

Validation gates, each at most once unless changed evidence justifies a retry:

1. Link the fixture against old 9cf archive as a negative control: unresolved
   split exports must fail linking, without fabricated stubs.
2. Confirm the new archive defines each split export exactly once and still
   supplies the existing real directory provider; reject duplicate owners.
3. Compile/link the fixture with the new archive using the canonical GNU hosted
   link libraries. Run it under normal bounds; all assertions, cleanup and
   `tls_workers=24` must succeed. Source existence is not a passed test.
4. Reuse the immutable seed and original normal object cache for the same build
   inputs. Let normal key validation choose hits; never rename/rekey objects.
   Regenerate link inputs with the new runtime and record remaining unresolved
   exports honestly. This repair does not qualify the other missing names.
5. The newly linked compiler must compile and run real Hello, including actual
   SCV snapshot creation and its existing physical-parent/revalidation gates,
   before any dependent compiler-stage qualification. No mkdir fallback,
   bypassed storage authority, unsafe stage marker, or codec retry is allowed.

## Actual retained Windows evidence

Evidence root: `C:/dev/simple-secure-temp-split-storage-20261024`. All executed
routes retained exact argv, clean environment, source/tool/archive hashes,
bounded collector status, and independent RSS/quiescence receipts. Each used
24 job slots and the normal 5,859,375-KiB aggregate guard. Reviewed production
files and the fixture remained unchanged during all runs.

- `old-negative-link`: launcher exit 89 before workload start because the MSYS
  watchdog's absolute Windows script path broke sibling helper discovery.
  No compiler ran. The next launch used a relative forward-slash script path.
- `old-negative-link-attempt2`: actual Clang/lld exit 1, exactly the three
  missing split exports and no other unresolved symbols. Old archive 9cf
  remained immutable; peak RSS 207,592 KiB, quiescent 1.
- `full-c-link`: standalone `runtime_native.c` compiled, but Windows linking
  required real canonical legacy/memory/SIMD helper providers. No assertions
  ran, no imports were fabricated, and that route was not retried.
- `new-positive-link` and `new-positive-run`: real Rust-boxed text plus the new
  narrow provider archive
  `dc022e2afae05a4e4be06413ef8ef81a1b46a329da480f4ee8e2cf2d43d6093a`;
  actual link/run exit 0, **1,385 assertions, 24 TLS workers**, quiescent 1.
  Link/run peaks were 171,412/40,276 KiB.
- `canonical-full-c-build`, `canonical-full-c-link`, `canonical-full-c-run`:
  all 28 unconditional source inputs from the real `tools.rs` assembly owner
  compiled and archived in original order, with its exact GNU flags and
  `SIMPLE_CORE_C_STANDALONE=1`/`SIMPLE_RUNTIME_MEMORY_OWNER=1`. No Rust archive,
  optional trap providers, or duplicate/unresolved-symbol allowances. Build,
  link and run exited 0, quiescent 1; the same fixture completed **1,385
  assertions, 24 TLS workers** with the real full-C boxed-value owner. Peaks
  were 1,175,064/125,884/44,348 KiB. Core-C archive SHA-256:
  `5809fc72cccb09644ed47247c1a8d5e1244f4f68cb2bff964df670d24ec3732c`.

Both successful runs checked the expected nonexistent-parent OS refusal,
consumption and invalid-after-valid semantics, protected ACLs, Unicode and
paths beyond MAX_PATH, TLS isolation and cleanup. Fixture SHA-256:
`8c39aff58f9db4548a96ec37af4990aa086a4bc0850e1b74cb68c4aad53f4032`.
The separate runtime-only Cargo owner reported exit 0/quiescent 1 and exactly
one definition of each required core/split export before issuing the new
immutable native-all archive. No seed executable was rebuilt for this repair.

Normal cached compiler relink and actual Hello qualification remain separate
pending gates. POSIX execution remains pending; Windows results do not qualify
the POSIX implementation or the remaining generated runtime stubs.

The official landing patch preserves newer release runtime context; the native
artifacts above bind the frozen eadb inputs, not a rebuilt release tree. The
existing archive-symbol guard now requires the two original and three split
exports exactly once. Its shell syntax was checked; its Unix compile/archive
route was not executed locally.
