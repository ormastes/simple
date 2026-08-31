# SimpleOS WM Vulkan smoke rows: blockers per arch (2026-08-31)

Goal item: "SimpleOS window manager with Vulkan-backed smoke tests on x86_64,
aarch64 and riscv64" — three rows. This record states, per arch, exactly what
blocks a **non-vacuous** pixel-evidence gate, so no later lane re-derives it.

## Architecture (do not misquote)

There is **no in-guest Vulkan in SimpleOS** and there never was. What exists is
a guest -> host **offload**: the guest WM encodes draw IR, publishes it through
an ivshmem BAR, and the host daemon (`src/app/simpleos_gpu_host/`) executes it
on a real host GPU. "Vulkan-backed" therefore means *the host daemon rendered
it and the guest holds a verified receipt*. The dual receipt is
`HOST_GPU_DAEMON_DRAWIR` (`daemon_runner.spl:413`, printed only when
`device_backed` holds) matched against the guest serial receipt on the nonce
`(frame, submit_id, fence_id)`.

Host capability was measured on this box, not assumed: TITAN RTX + RTX A6000,
Vulkan **1.4.312**; `ivshmem-plain` present in both `qemu-system-x86_64` and
`qemu-system-aarch64`; OVMF, AAVMF and `QEMU_EFI.fd` all installed;
`vendor/limine/BOOTAA64.EFI` present. **None of these is the blocker for any
row.** Any claim of "no GPU on this host" is false.

## x86_64 — blocked on build cost, not on a defect

The closure is complete: PR #188 restored
`std.common.contracts.os.server_data_namespace_v1` and added the previously
missing producer
`scripts/os/build-simpleos-x86-64-desktop-engine2d-kernel.shs`; PR #186 fixed
the gate's unsatisfiable classifier. The gate's own selftest is green here:

    PASS — 17 selftest fixture(s) checked, classifier and pixel bar behave
    (no boot attempted), renderer=n/a

The `vulkan,cuda,runtime-symbol-table` runtime archive builds clean
(`RUNTIME_RC=0`, 101 MB). The remaining cost is the host daemon
`native-build`, which on this shared box (load 10-15) advanced 4 of 96
surfaces in 8.5 minutes — hours, not minutes. The prior lane's failure
(`daemon-build4.log`, "native-build worker exited with code 1") was **not**
reproduced: with the correct invocation — the one
`check-simpleos-qemu-host-gpu-2d.shs` uses, `--runtime-bundle core-c-bootstrap`
plus `SIMPLE_LINK_OBJECTS=<vulkan/cuda archive>` — the build proceeds normally.

Nothing here needs a code fix. It needs a machine and a long enough timeout.

## aarch64 — HARD blocker: no compiler on this host can build the kernel

Two real source defects were found and **fixed** (see commits below); the row
is still blocked behind a third thing that is not fixable in source.

`examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl` was a
casualty of clobber `4edef8fab8e` — 525 lines against 589 pre-clobber:

1. **Did not parse at all.** Lines 433-438 duplicated the
   `WmAction.FocusWindow` arm at +4 indent and every later arm inherited the
   wrong indentation. Fixed surgically (not by restore: the two blobs diverged
   in *both* directions, 196 lines only in pre against 132 only in current).
2. **Dangling references from a half-finished rewrite.** The file replaced the
   `Arm64ProductionWmProducer` publication path with direct surface
   materialization but left `published_snapshot` (used, never declared) and
   `animation_surface_id` (never declared) behind. All 16 blobs in git history
   carrying the rewrite marker, and the copies in three other worktrees, have
   no `published_snapshot` declaration — the text was never written, so it is
   not recoverable. Repaired minimally: the three dead vars at 315-317 are
   deleted (declared, never read), `animation_surface_id` -> `editor_id`.

3. **The remaining blocker.** With both fixed, the Rust seed still fails:

       hir: Unsupported feature: cannot infer field type while lowering
       gui_entry_desktop_start: struct 'ANY' field 'delivered_key_sequence'

   The source is correct — `Arm64VirtioInputBackend.create(i64, i64) ->
   Arm64VirtioInputBackend` is declared at
   `src/os/compositor/arm64_virtio_input_backend.spl:108` and
   `delivered_key_sequence: i64` is a real field at `:78`.

   Two candidate workarounds were tried and **both failed**, which is what
   makes this a compiler limitation rather than a source problem:

   - An explicit type annotation on the binding
     (`var input_backend: Arm64VirtioInputBackend = ...`). The compiler's
     guess merely changed from `RocmFfi` to `ANY`; it still failed.
   - Restoring the pre-clobber call form
     `create_with_poller(w, h, arm64_virtio_input_poll, false)` — the
     hypothesis being that `create` collides with the `static fn create` on
     other structs (e.g. `HostedInputBackend`) while `create_with_poller` is
     unique, so the pre-clobber form would resolve. It **fails identically**,
     with the same `struct 'ANY' field 'delivered_key_sequence'`. The
     name-collision hypothesis is therefore **disproven**: inference fails on
     this struct regardless of which constructor is called.

   Both experiments were reverted rather than left in as workarounds that do
   not work. (Note in passing: the file still imports `arm64_virtio_input_poll`
   at line 17 and never uses it — more evidence the rewrite is unfinished — but
   wiring it changes nothing here.)

   This is consistent with, and is the concrete mechanism behind,
   `check-simpleos-arm64-unified-live.shs:70` refusing a `Rust-built` compiler
   outright (`fail compiler-is-bootstrap-seed`). That lane needs the
   pure-Simple compiler.

   **And no pure-Simple compiler is deployed on this host.**
   `bin/release/x86_64-unknown-linux-gnu/simple` resolves to a binary that
   itself prints "this Rust-built Simple binary is a bootstrap seed only", and
   there is no `.provenance.env` beside it. So the aarch64 row cannot be built
   by any compiler currently on this machine.

   Unblocking needs a bootstrap deploy of a pure-Simple full CLI, or a seed HIR
   fix for this inference case. Not a gate-authoring problem.

Note separately: even once it builds, `check-simpleos-arm64-unified-live.shs`
boots with QEMU `-kernel`, which `.claude/rules/board-runnable.md` forbids. The
kernel-side half of the EFI migration is already done
(`check-simpleos-arm64-unified-boot-contract.shs`); the lane edit is not.

## riscv64 — NOT feasible; needs new code, not a gate

Three independent layers are missing. A gate written today would be vacuous,
so none was written.

1. `examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl:118`
   calls `create_host_gpu(...)` with `SIMPLEOS_HOST_GPU_BACKEND_METAL` and
   `backend_required=false`. It degrades silently to CPU and can never emit a
   `backend=vulkan` DrawIR receipt. No `SIMPLEOS_HOST_GPU_BACKEND_VULKAN`
   reference exists anywhere under `arch/riscv64/`.
2. **No producer builds a riscv64 desktop/WM kernel ELF at all.**
   `scripts/os/build-simpleos-riscv64-components-kernel.shs` builds components,
   not the GUI entry. The only thing that touches a riscv64 desktop entry is
   the PowerShell `check-simpleos-qemu-rv64-desktop-evidence.ps1`, and it
   builds `desktop_service_entry.spl` — a different, non-WM entry.
3. No riscv64 QEMU lane passes `ivshmem`. Every lane that does
   (`arm64-unified-live`, `x86-64-wm-host-vulkan-pixel-evidence`,
   `qemu-host-gpu-2d`, `qemu-guest-gpu-passthrough`, `io-audio-qemu`) is
   x86_64 or arm64.

The bridge itself is **not** the obstacle: `src/os/lib/gpu_bridge/
host_gpu_ivshmem.spl` has no arch conditionals — ISA is a wire field (`:185`,
`:197`) — and `arch/common/host_gpu_ivshmem_probe_entry.spl` is arch-generic
with backend/required as parameters (`:162-165`).

Order of work: (a) switch the riscv64 entry to VULKAN/required, mirroring
arm64's parameterized `gui_entry_desktop_start`; (b) add a
`scripts/os/build-simpleos-riscv64-desktop-engine2d*.shs` producer; (c) add
ivshmem + QMP to a riscv64 OpenSBI `-bios fw_payload` lane. Only then is a gate
worth writing.

Related: `doc/08_tracking/bug/board_vulkan_cross_arch_boundary_only_x86_64_proven_2026-08-11.md`
already records that `check-simpleos-riscv64-opensbi-real-firmware-boot.shs`
boots OpenSBI with **no guest payload** and proves nothing Vulkan-relevant.

## Status

| arch | row | blocker |
|---|---|---|
| x86_64 | not yet proven | daemon `native-build` wall time on a loaded box; no defect found |
| aarch64 | not done | seed HIR inference failure + no pure-Simple compiler deployed on this host |
| riscv64 | not done | METAL-hardcoded entry, no producer, no ivshmem lane — new feature work |

No vacuous gate was authored for any row.
