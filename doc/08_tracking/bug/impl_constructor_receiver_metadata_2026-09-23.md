# Impl constructor-name receiver metadata

Status: OPEN / PARTIAL_VERIFICATION. Independent review accepted the shared
parser correction; eight parser tests and CUDA native execution pass. Intel
and ROCm compile past the receiver failure but cannot link against the frozen
runtime capsule. Full Phase 2 and bootstrap admission remain unverified.
No production GPU provider implementation is changed.

## Evidence and root

Fresh admitted Stage 2 compiler SHA-256
`98cbcdb15be2d04223bc03dd6ace3982b9e7826fbca9ec76e83a096f7a437cf3`,
source `e52ef0cc249d2e49b4d9d66070edd37ce269b4cc`, failed the Phase 2 full CLI
build in the three canonical `src/lib/nogc_sync_mut/gpu/engine2d/` owners
`sffi_cuda.spl`, `sffi_intel.spl`, and `sffi_rocm.spl`. Each `init` body failed
with `GlobalLoad: unresolved identifier 'self'`. Strict no-stub policy correctly
rejected these objects; this is not a CUDA/Intel/ROCm native ABI failure.

Exact retained log:
`/Users/ormastes/simple-tmp/macos-phase2-receiver-admission-20260923/build/evidence/phase2-receiver-stage2-capacity-retry/logs/compiler_cli_build.log`
(first errors at lines 46-51; failed files at lines 73-75).

`parser/src/types_def/trait_impl_parsing.rs` inferred static methods from the
names `init`, `new`, `create`, `default`, and `from_*`, even when the method had
an explicit receiver or used `self` in its body. The receiver admission fix in
PR #1380 made HIR trust parser metadata, exposing this remaining impl-parser
misclassification. Imported declarations must contain the receiver before ABI
arity is recorded; repairing it later in HIR would recreate the arity defect.

## Scoped correction

Only infer a static factory when it has no leading explicit receiver and its
body does not use `self`. Explicit `static` declarations remain authoritative;
mutable methods remain instances; the existing single receiver injection is
unchanged. Receiver-free factories retain their existing ABI.

This reuses the existing receiver walker. It does not expand that walker's
coverage of expression/node forms. In particular, self used only inside forms
the walker does not visit remains a separate limitation; no general parser
parity or full-language receiver claim is made.

## Verification plan and limits

- Extended `parser/tests/implicit_receiver_metadata.rs`: all five factory-name
  patterns, inherent and trait impls, explicit receivers without body use,
  receiver-free factories, and explicitly static declarations.
- Production-owner native fixtures: `cuda_ffi_init_receiver`,
  `intel_ffi_init_receiver`, and `rocm_init_receiver` under `test/fixtures/native/`.
  These exercise imported instance `init` with a nil dynamic library and assert
  fail-closed results, method dispatch, and static-factory mode. They do not
  establish GPU hardware availability or native driver operation.
- Baseline admitted compiler must reproduce the failure; a freshly built and
  separately qualified compiler containing this parser change must pass the
  same fixtures with `SIMPLE_NO_STUB_FALLBACK=1`. Never label the unchanged
  admitted compiler as containing this fix.
- Record compiler/source hashes, runtime capsule, commands, elapsed time, and
  process-tree RSS. Do not share writable caches between compiler lineages.
- Full Phase 2 CLI and runner remain separate admission gates, including the
  independent GUI failure already present in the retained baseline log.

No builds were launched during the matrix run or subsequent disk-capacity hold.

## Initial review and baseline reproduction

Independent Astra reviewer `/root/fix_phase2_intel_init` accepted the source and
parser-test design. This is a static review, not an execution PASS.

The ROCm fixture owner separately reproduced the sole `RocmFfi.init` unresolved
receiver failure with the admitted compiler: exit 1, 4.15 seconds elapsed,
113552 KiB sampled process-tree peak against a 976562 KiB enforced cap,
observer errors 0, quiescent 1. Preserved evidence:
`/Users/ormastes/simple-tmp/phase2-rocm-init-20260923/build/native_probe/rocm-init-receiver/stage2-98cbcdb15be2d042/`
(`red.log`, `red.env`, `red.time`). The original fixture used the `std` alias;
the central fixture imports the canonical owner explicitly. These are source
equivalent owner routes, but the central fixture still needs its own native
qualification. This baseline result alone establishes no green result.

## Parser execution after disk recovery

Source commit `d1be2cca0f7e2bba24e699713e959423919ae4cf` passed all eight
`implicit_receiver_metadata` parser tests in 40.20 seconds. Sampled process-tree
peak: 825264 KiB; enforced cap: 5859375 KiB; observer errors: 0; quiescent: 1.

Private pinned toolchain:
`/Users/ormastes/simple-tmp/rustup-pinned-20260916.kq7xQk/rustup/toolchains/nightly-2026-09-16-aarch64-apple-darwin`.
Absolute rustc SHA-256:
`76470bf06f36ddea8135caeb96efe7fd67896c9331317e8d40369ed002fe408a`;
Cargo SHA-256:
`b87b3b4e204be097e048a93c5b45d50d3708a8ef342027232457abc31d945e20`.
These match the previously independently qualified private dated toolchain.
No floating rustup proxies or shared-toolchain modification were used.

Evidence root:
`/Users/ormastes/simple-tmp/phase2-cuda-init-20260923/build/evidence/impl-receiver/`.
`authority.sha256`, `owner-inputs.sha256`, `run-cargo.shs`, `parser.log`, and
`parser.rss.env` retain inputs, exact commands, and telemetry. Tests ran with
`cargo test --locked --offline -p simple-parser --test implicit_receiver_metadata`
using an isolated target and one Cargo job. The production runtime capsule
also passed its immutable verification check (`capsule-verify.log`).

## Corrected compiler and native owner results

The pinned diagnostic compiler built successfully in 225.67 seconds with
3207344 KiB sampled process-tree peak, observer errors 0, quiescent 1. Its
SHA-256 is `cb26939ab543dccad92dd0494964726cfa5f6067389018a3f51d2db18d27b01f`.
The build used `--locked --offline --profile bootstrap --target
aarch64-apple-darwin -p simple-driver --features llvm`, one Cargo job,
bootstrap LTO off, and 16 codegen units, matching the bounded diagnostic
configuration used for the preceding receiver fix. Source was `d1be2cca0f7`;
subsequent changes only reduce the CUDA fixture to its receiver scope and
update this report.

Known nonfatal `rust-objcopy` stripping failures reported the missing
`@rpath/libLLVM.dylib`. This executable is diagnostic evidence, not an admitted
bootstrap compiler or release artifact. No full-suite, throughput, or memory
regression claim follows from this compile.

All native fixtures used `SIMPLE_NATIVE_BUILD_RUST=1`,
`SIMPLE_NO_STUB_FALLBACK=1`, no allow-stub override, the verified frozen
98cbcdb runtime capsule, one native worker, and separate compiler/fixture caches.
Native sampled enforcement was 976562 KiB. All terminal receipts have observer
errors 0 and quiescent 1.

| Fixture | Actual result | Elapsed | Peak KiB |
| --- | --- | --- | --- |
| CUDA cycle 2 build | PASS | 3.38 s | 279200 |
| CUDA cycle 2 execution | PASS, four assertions | 0.39 s | 2400 |
| Intel cycle 1 | Receiver codegen succeeds; link FAIL | 4.87 s | 288736 |
| ROCm cycle 1 | Receiver codegen succeeds; link FAIL | 5.51 s | 278304 |

CUDA cycle 1 compiled the owner but failed linking `rt_cuda_shutdown`, which
was reached only by an extra shutdown assertion. That unrelated assertion
was removed; the four retained assertions cover instance init returning false
without a library, dynamic mode, availability false, and static factory mode.
The initial failed build log and cache were retained. CUDA cycle 2 passes with
the original production provider code. `cuda-cycle2-input.sha256` identifies
the final fixture; `owner-inputs.sha256` retains the original inputs.

Intel fails to link `rt_intel_is_available`, `rt_intel_init`, and
`rt_intel_shutdown`. ROCm fails to link the corresponding `rt_rocm_*` names.
Neither executable ran. These are separate runtime-link boundary failures,
not evidence that the receiver error persists. Intel's owner documents its
unimplemented static runtime backend. Read-only ROCm follow-up found its real
hooks in the native archive, so ROCm archive selection/export diagnosis remains
open; this log does not establish missing ROCm implementation.
No replacement hooks or empty
stubs were introduced, and neither result is labeled native PASS.

Exact logs and receipts are under
`build/evidence/impl-receiver/native/cb26939ab543dccad92dd0494964726cfa5f6067389018a3f51d2db18d27b01f/`
in this worktree; CUDA's accepted attempt is `cuda_ffi_init_receiver/cycle2`,
and Intel/ROCm blocked attempts are their respective `cycle1` directories.
`run-owner.shs` retains the full native commands. The independent Astra reviewer
confirmed parser/CUDA evidence and required the Intel/ROCm execution blocker
to remain explicit. No passing gate was rerun.
