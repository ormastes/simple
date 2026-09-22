# Phase2 Vulkan pipeline/present/push loader ABI

Scope: sidecar P, all 13 rows of the frozen GPU-loader partition. Baseline
`e6ffda6849e6aa7fe01a7d23ddc71e9773286532`. This is synthetic native ABI proof,
not physical GPU, full-runner, compiler-matrix or Phase3 admission evidence.

## Change

`src/runtime/runtime_gpu_vulkan_pipeline_private.h` supplies the missing core-C
symbols. Include it after the checked array helper in `runtime_dynload.c`.
Every provider operation uses the existing acquire/release call pin; provider
code runs without the registry lock. Scalar statuses, including unavailable
copy-statistic `-1`, are preserved. The GLSL operation remains unsupported:
its optional provider diagnostic is invoked with ignored argument zero and
the result is always zero, even if the provider incorrectly returns success.

Core text is decoded with core accessors, bounded to 4096 bytes, rejects NUL,
then loaned to the raw provider entry-point operation. Push sizes fit u32.
Push constants use checked core byte extraction, bounded to the provider's
64 MiB limit before allocation; explicit count must fit the owner. Empty
arrays use a nonnull call-scoped zero-length loan. Regions use main-owned
`rt_array_i64_validate`/`rt_array_i64_copy_checked`, at most 1024 four-field
rectangles, range-check u32 fields and dimensions, and encode every i64 field
little-endian. The bounded scratch allocation is at most 64 KiB. Temporary
buffers are freed on success, rejection and provider absence.

Dependencies intentionally owned by the merge owner, not this commit:
the checked byte helper in `runtime_dynload.c`; checked signed-i64 array APIs
in `runtime_native.c`/`runtime.h`; the actual fragment include and runtime
fingerprint integration. No registry admission, provider-required list or
cross-sidecar file was edited here.

## Native evidence

Evidence directory (retained locally):
`build/native_probe/phase2_gpu_vulkan_pipeline_cycle1/`.
Producer is admitted Stage2 SHA256
`0c65162af9c89bdb9c6583ca91820f795231c9bf4c451b6a69ea66794c66c084`,
with its same-SHA runtime capsule. That admitted compiler invocation uses the
Rust-delegated `--emit-archive` route (`SIMPLE_NATIVE_BUILD_RUST=1`); this proves
an actual compiled Simple ABI boundary, not the self-hosted frontend. It is
bootstrap-only narrow fixture evidence, not substitute compiler-test evidence.
Compilation: one unit, zero failures, 0.2 s;
peak sampled tree RSS 58,912 KiB, no observer errors, quiescent completion.
`identities.txt` binds producer, capsule receipt, main-owned runtime snapshots
and the sidecar fragment. The full compiler test runner was not built here.

The real Simple fixture sends text, a `[u8]` owner containing 0/8/127/255,
an empty byte array, and `[i64]` rectangle fields crossing byte boundaries
(255/256/257/258). A synthetic dylib validates exact arguments, byte order and
length. The C harness additionally checks every scalar forward, entry length,
interior NUL, size overflow, malformed boolean/byte record arrays, invalid
dimensions, unchanged provider call count on rejected inputs, and valid loans
when the provider is absent. The unsupported GLSL provider deliberately returns
999; the caller still observes zero, and the provider diagnostic flag is set.

Baseline loader link fails on the assigned missing symbols
(`baseline-link-clean.log`). With the fragment, `check-cycle3.log` records:
`phase2_gpu_vulkan_pipeline=PASS native_boundary=1 lease_reentry=1 unload=1`.
The present provider re-enters core unload while pinned: unload reports busy,
the active call finishes, new calls fail during retirement, and final unload
drains successfully. No borrowed provider memory escapes this slice.

Mutation: a private copy of the production fragment changed the rectangle
encoder shift from `j * 8` to `(7 - j) * 8`; relinking only that loader against
the unchanged native fixture causes `native_probe=9`, exit 1 (`mutant.log`).
This establishes that the Simple-to-provider byte-order oracle is non-vacuous.

Final repeated native probe cost: 1001 total probes, loop CPU 0.003691 s,
maximum resident size 3,194,880 bytes, sampled tree peak 2,432 KiB. Observer
errors/restarts zero, `quiescent=1`, cap 5,859,375 KiB. This measures a bounded
synthetic workload, not physical GPU latency or leak freedom; no before/after
speedup is claimed because the baseline could not link the operations.
`hard_memory_limit=0`: sampled enforcement only.

Initial harness-only repairs: expose Darwin `RTLD_DEFAULT`; export only the
unload callback instead of keeping every runtime symbol live; use the macOS
legacy per-symbol fixture path instead of unsupported immutable-v1 digest
admission. All failed logs are retained. No production adapter fix was needed
after executable testing. The final third scoped verification completed PASS.

## Reproduce and integrate

Run `sh scripts/check/check-phase2-gpu-vulkan-pipeline.shs COMPILER CAPSULE
SHARED_OWNER NEW_OUTPUT_DIR`. The checker snapshots main-owned runtime files,
builds the actual Simple archive through the Rust-delegated
`--emit-archive --no-mangle` route, links the
synthetic provider and native harness, retains the baseline missing-symbol
failure, and runs under the sampled RSS watchdog. The `PHASE2_GPU_PIPELINE_RESUME=1`
option verifies recorded hashes and reuses its already-built native archive
for a failed harness setup retry; do not rerun unchanged green checks.

Independent Astra reviewer `/root/stage2_after_progress_fix/pipeline_abi_review`
reported scoped PASS: public ABI, sentinels, bounds, conversion, cleanup and
lease paths have no blockers. Review explicitly excludes hardware/V1 claims
and treats repeated probes as cost evidence, not allocation instrumentation.
The merge owner must include the fragment, integrate its shared array helpers,
run the combined native boundary gate and GPU-symbol census, and only then
request the separately controlled full runner rebuild.
