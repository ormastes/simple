# SimpleOS WM Vulkan/Sosix QEMU Follow-up Plan

Updated: 2026-08-11

## Decision and boundary

The current production-capable diagnostic route remains:

`DrawIrComposition -> SimpleOS host-GPU codec -> ivshmem -> host daemon -> Vulkan/Engine2D readback`.

Sosix is **not** a substitute transport in this plan. Its dataset/queue APIs
are not initialized by the ARM64 or x86_64 desktop entries, and the
`SIMPLE_SOSIX_GPU_LANE` Engine2D model has no production call site. A future
Sosix bridge needs separate approved requirements and must preserve the
ivshmem receipt/readback boundary below.

The on-board SimpleOS GPU driver is VirtIO DMA/present, not a Vulkan compute
driver. Consequently, a Vulkan host-GPU result cannot be relabeled as a native
board-Vulkan result.

## Current status

| Area | Status | Evidence boundary |
|---|---|---|
| QEMU host-GPU Vulkan protocol | Source and retained cached receipts exist | Fresh run remains blocked by a current admitted self-hosted compiler. |
| ARM64 WM RAMFB drawing | Source route exists | Requires a current strict ARM64 artifact and one bounded QMP/RAMFB run. |
| ARM64 producer/QMP manifest schema | Reconciled on synced `origin/main` | The producer and consumer agree on the strict `os build --scenario=arm64-desktop-engine2d` command/environment; the focused contract spec passes. |
| macOS ARM64 QEMU acceleration | Ready for later launch | `/opt/homebrew/bin/qemu-system-aarch64 -accel help` reports `hvf`; launch remains closed until the required kernel, disk, and manifest exist. |
| Fresh AArch64 compiler bootstrap | Strict Stage 2 attempt failed; source fix pushed | The 2026-08-11 attempt exposed ambiguous ABI method dispatch. `76c949f095` supplies the focused source fix; a fresh non-seed rerun still needs complete provenance, strict no-stub receipt, and module-global identity. |
| Board-Vulkan seam | Refactor state must be rechecked before integration | A concurrent review observed transient board-Vulkan/WM-host deletions; the current Git diff no longer shows those paths, so ownership and intended replacement must be confirmed in the isolated source state. |
| Sosix to WM/Vulkan | Not implemented | No `sosix_init` desktop call and no real dataset/queue bridge. |

## Ordered work

1. **Ownership gate — `/root` + refactor owner**
   - Recheck whether any board-Vulkan and WM-host file removals are an intentional replacement or an incomplete refactor, then identify its owner.
   - Do not restore, build, commit, or launch QEMU from the mixed workspace.
   - Finish or recover the seam in an isolated worktree with a single owner.

2. **Compiler admission — compiler owner**
   - Produce a current pure-Simple Stage 2/3-or-newer artifact with complete provenance, module-global identity, `SIMPLE_NO_STUB_FALLBACK=1`, and the strict fabricated-stub ratchet.
   - Reject copied, renamed, Rust-seed, debug, missing-receipt, fabricated, or stale artifacts.
   - Current failure record: the 2026-08-11 sibling Stage 2 attempt rejected ambiguous untyped `contract.abi.to_text()` dispatch in `src/compiler/70.backend/backend/llvm_target.spl`; replacing those six uses with the typed `contract.abi_text()` contract passes the focused interpreter regression in an isolated worktree. Re-run native admission only from a non-seed pure-Simple compiler. The later Stage 3 `env_ops.host_arch` void-to-`i64` failure came from a sibling-local dirty `if/elif` form; it is not established against synced current source and must not be promoted as an upstream compiler defect without a clean reproduction.

3. **Vulkan/QEMU diagnostic evidence — exclusive QEMU owner**
   - Use the existing ivshmem codec and canonical host-GPU wrapper only after Step 2 passes.
   - Retain the QEMU `MAP`, `HELLO`, DrawIR/ProcessingIR, Vulkan archive, readback, and final correlation receipts. Cached receipts remain historical, not fresh PASS evidence.

4. **ARM64 WM evidence — exclusive QEMU owner**
   - Build the ARM64 desktop in isolated outputs from the admitted compiler.
   - Run exactly one bounded QMP/RAMFB capture sequence and retain source, compiler, kernel, disk, serial, QMP, and before/after image identities.
   - Do not claim physical Cocoa input requirements from QMP injection.

5. **Optional Sosix bridge design — design owner, only after approval**
   - Specify an explicit early `sosix_init`, sealed DrawIR dataset, bounded notification queue, ownership/lifetime rules, and ivshmem conversion.
   - Prove it with the same live QEMU receipt/readback contract; an env-gated host-side model is not an implementation.

## Exit criteria

- The active board-Vulkan/WM refactor has one documented owner and clean isolated source state.
- A current compiler admission receipt passes strict no-stub checks.
- One fresh ARM64 QMP/RAMFB run has correlated guest and host artifacts.
- Any future Sosix bridge has an approved design and real `os.sosix` runtime integration; otherwise it remains explicitly out of scope.
