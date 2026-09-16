# In-guest Vulkan does not exist in SimpleOS; every WM smoke frame is CPU-rendered

Date: 2026-08-31
Scope: goal item 2 — x86_64 / arm64 / riscv64 SimpleOS window-manager smoke tests
with a "Vulkan-backed 2D path".

## Verdict

**There is no in-guest Vulkan path.** Any SimpleOS window-manager frame captured
today — on any of the three architectures — is **CPU-rendered**. Labelling such a
frame "Vulkan-backed" would be false.

What exists instead is a *third* thing, neither in-guest Vulkan nor plain CPU: a
**guest -> host ivshmem offload** with a genuine host-side Vulkan daemon. It is
real, but it does not render the window manager and it does not boot under real
firmware. Details below.

## Evidence (three independent confirmations)

1. **The compositor's Vulkan backend rejects all drawing by contract.**
   `src/os/compositor/backend_factory.spl:77-83` registers `ScreenType.Vulkan` ->
   `VulkanCompositorBackend`, and its own comment states
   `VulkanCompositorBackend.is_available()` is unconditionally false. The backend
   file (`src/os/compositor/vulkan_compositor_backend.spl:12`) carries an explicit
   honesty contract: *"No method here talks to a GPU, a venus ring, or any Vulkan
   API."* Its only real probe is `is_char_device(render_node)` — a stat(2)
   `S_ISCHR` test that any character device (e.g. `/dev/null`) passes, and which
   the file itself says callers "must not read as 'Vulkan works'". Drawing remains
   rejected regardless of the probe result.

2. **Every `rt_vulkan_*` entry point is compiled out inside the guest.**
   `examples/09_embedded/simple_os/arch/x86_64/boot/freestanding_optional_backends.c:120-132`:
   *"Host Vulkan SFFI is unavailable inside SimpleOS. The guest's framebuffer path
   remains authoritative; any accidental host-Vulkan operation fails."* Twelve
   `rt_vulkan_*` symbols are defined as `UNAVAILABLE(...)` / `ABSENT(...)` stubs.
   This is a link-level guarantee, not a runtime policy.

3. **The baremetal 2D engine has zero Vulkan references.**
   `src/os/compositor/engine2d_baremetal_core.spl` — the in-guest rasteriser —
   contains no Vulkan symbol of any kind. Real Vulkan under `src/os/` lives only in
   host/board ports (`src/os/port/qrb2210_*vulkan*`, `src/os/hosted/hosted_entry.spl`)
   and in the host-offload adapter (`src/os/lib/gpu_bridge/vulkan_host_offload_adapter.spl`).

## The host-offload path: real Vulkan, wrong shape

`scripts/check/check-simpleos-qemu-host-gpu-2d.shs` (3231 lines) is *not* a
fail-open proxy. It links the host runtime with the `vulkan` cargo feature,
requires the `rt_vulkan_provider_is_available` / `rt_vulkan_init` /
`rt_vulkan_compile_spirv_raw` / `rt_vulkan_create_compute_pipeline` symbols to be
present, runs `src/app/simpleos_gpu_host/` as a daemon, and asserts a
`HOST_GPU_PROCESS_OK isa=<isa> backend=vulkan` receipt plus a 1280x720 pixel
checksum (`HOST_GPU_FIXTURE_CHECKSUM=1417723768`, 633600 background + 288000 rect
pixels). That is genuine GPU rendering with pixel assertions.

Two reasons it does not satisfy this goal:

- **It is not the window manager.** It renders a 2D fixture through
  `host_gpu_ivshmem_probe_entry.spl`, not a WM frame. (The WM frame executor *does*
  support the path — `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl:598`
  calls `Engine2dWmFrameExecutor.create_host_gpu(..., SIMPLEOS_HOST_GPU_BACKEND_VULKAN, ...)`
  — so wiring the WM to it is plausible future work, not a rebuild.)
- **It boots the guest with `-kernel -nographic`, violating `.claude/rules/board-runnable.md`.**
  This is not incidental: the gate's own argv validator *requires* `-kernel` at a
  fixed argv position (lines 1306, 1334, 1350, 1366, 1377), so `-kernel` is the
  encoded contract of the lane, not a stray fixture. Migrating it onto OVMF/EDK2/OpenSBI
  is a separate, sizeable piece of work.

`check-rv64-display-smoke-qmp-evidence.shs:514-515` has the same defect in milder
form: `-bios default` (OpenSBI) *plus* `-kernel`.

## What in-guest Vulkan would require

Extends, does not duplicate,
`doc/08_tracking/bug/simpleos_vulkan_board_gap_venus_is_qemu_only_2026-08-06.md`
and the G0/G1 plan `doc/04_architecture/os/vulkan/simpleos_vulkan_render_backend_plan.md`.

1. A virtio-gpu PCI/MMIO driver in the guest that negotiates the **venus** capset
   (protocol negotiation `vulkan_compositor_backend.spl` explicitly does not
   implement). Today's `detect_virtio_gpu_device` is a `stat` call — see
   `doc/08_tracking/bug/vulkan_detect_virtio_gpu_device_is_existence_check_not_device_probe_2026-08-07.md`.
2. A venus command-ring encoder in pure Simple (no new `rt_*` in C/Rust per repo
   rule), plus guest-side DMA-BUF/shmem allocation for the ring and for images.
3. Removal of the `UNAVAILABLE()` stubs in `freestanding_optional_backends.c`
   *only after* 1-2 exist; today they are the correct fail-closed behaviour.
4. A board story. venus is QEMU-only on the research host, so a board-runnable
   claim needs a real Adreno/Mali/DRM path — closer to the existing
   `src/os/port/qrb2210_adreno_vulkan_kernel_transport.spl` than to venus.

Until 1-4 land, the honest label for any SimpleOS WM frame is `renderer=cpu`.

## Related fail-open already filed

`doc/08_tracking/bug/engine2d_vulkan_window_8k_gate_is_device_present_proxy_2026-08-31.md`
— `check-engine2d-vulkan-window-8k.shs` passes via `scope=xvfb-device-present-proxy`
with `readback_bytes=0` and captures no pixels. Same failure mode this record exists
to prevent.

## Blocker hit while producing pixel evidence

The x86_64 WM lane (`check-simpleos-x86-64-wm-hello-lifecycle-evidence.shs`) refuses
to run without an **admitted Stage-2 compiler**: `SIMPLE_BIN` defaults to
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple` and is
gated by `simpleos_admitted_runtime_verify_auto`
(`scripts/check/lib/simpleos-admitted-runtime.shs`), which requires an
`admission.env` receipt chain plus a live env-ABI probe. A stale deployed
`bin/release/.../simple` fails at exit 11 (`simple-bin-admission-or-env-abi-failed-11`),
and a bare `cargo build --release --bin simple` seed cannot satisfy it either —
it has no receipts. Producing WM pixel evidence in a fresh worktree therefore
requires a full bootstrap first.

## Measured this session (2026-08-31)

Base: worktree merged `goal/simpleos-b1-merge-clobber-restore-20260831` (`91b6b9f28dd`)
onto `b0be388ec46`. Seed rebuilt from source (`cargo build --release --bin simple`,
green, 61,018,016 bytes).

| arch | kernel built | booted (real firmware) | WM up | pixels | renderer |
|---|---|---|---|---|---|
| riscv64 | yes | **PASS** | not attempted | none | n/a |
| x86_64 | not attempted | blocked | blocked | none | n/a |
| arm64 | **FAIL (link)** | blocked | blocked | none | n/a |

riscv64 verdict line, verbatim:

```
[guest-boot] selftest OK (4 fixtures)
PASS — 8 marker(s) checked, riscv64 guest kernel (real crt0.S + linker.ld) booted
under real OpenSBI v1.4 firmware via -bios fw_payload (no -kernel, no isa-debug-exit;
live SBI ecall + FDT handover verified;
serial: build/verify/simpleos-riscv64-opensbi-guest-boot/serial.log)
```

`check-rv64-display-smoke-qmp-evidence.shs` ran to completion but produced **no
pixels**: `rv64_wm_font_region_rgb_bytes=0`, empty sha256, and every WM marker
(`rv64_wm_guest_font_marker`, `rv64_wm_keyboard_correlated`,
`rv64_wm_pointer_correlated`, `rv64_wm_input_frame_changed`) is `0`. It is
therefore not usable as WM pixel evidence today, and it separately boots with
`-bios default` **plus** `-kernel` (line 514-515).

`check-simpleos-arm64-efi-real-firmware-boot.shs` correctly returned
`ERROR — nothing was checked` (fail-closed) for a missing
`build/os/aarch64_limine/kernel.elf`.

### New defect found: the C runtime is compiled for the HOST arch during a cross native-build

`scripts/os/build-simpleos-aarch64-limine-kernel.shs` passes
`--target aarch64-unknown-none-elf`, but the C-runtime step inside `native-build`
compiles `libsimple_runtime.a` for **x86_64** anyway:

```
clang: warning: 'x86_64' does not support '-mno-outline-atomics'; flag ignored
...
ld.lld: error: .../core_c_runtime/libsimple_runtime.a(runtime_native.o) is
        incompatible with .../_boot_freestanding_runtime.o
```

17 archive members are rejected as incompatible; the link fails and no
`kernel.elf` is produced. **Reproduced on two independent compilers** — the
freshly built cargo seed and the admitted Stage-2 binary from
`/mnt/data/worktrees/phase1-rerun` — with `.simple/native-objects-*` cleared in
between, so this is a build-system defect, not a stale artifact. It blocks the
entire aarch64 real-firmware lane (kernel -> ESP -> EDK2/AAVMF boot -> WM ->
pixels) at step one.

### Correction to the blocker scope

The admitted-Stage-2 requirement is specific to the **x86_64 WM lifecycle lane**.
The arm64 and riscv64 gates call no admission verifier
(`grep -c admitted_runtime_verify` = 0 on all four of
`check-simpleos-riscv64-opensbi-guest-boot.shs`,
`check-rv64-display-smoke-qmp-evidence.shs`,
`check-simpleos-arm64-efi-real-firmware-boot.shs`,
`check-simpleos-arm64-qmp-input-evidence.shs`) and need only a kernel artifact
that any working compiler can produce — which is why riscv64 reached a real PASS
this session and arm64 got as far as a link error rather than an admission wall.

## Follow-up (2026-08-31, same session): wiring the WM to the host-Vulkan offload

Objective: make the WM genuinely Vulkan-backed via the ivshmem host-GPU offload
and capture real WM pixels. Result: **the gate is built, proven by selftest, and
blocked on artifacts** — not on design. Findings below, in the order they bind.

### The WM-over-host-Vulkan lane already exists, and already asserts Vulkan

`check-simpleos-qemu-host-gpu-2d.shs` has an aarch64 "production" lane (lines
3002-3011) that builds the real WM desktop entry
(`arch/arm64/gui_entry_desktop_linux_qemu.spl` -> `simpleos_arm64_desktop_engine2d.elf`),
boots it with ivshmem plus the host Vulkan daemon, and asserts a correlated
receipt chain: `HOST_GPU_NEGOTIATION_DONE scope=production ... backend=vulkan`,
`[wm-frame] host-gpu-ready backend=vulkan generation=N`,
`[wm-frame] host-gpu-presented`, `[desktop-gui-arm64] desktop-ready`, with
generation continuity against the probe lane (`arm64_production_evidence_valid`,
line 1386).

So the WM **is** already Vulkan-backed via host offload. The gap this task
targets is narrower than "wire it up": that lane runs `-nographic` and asserts
**serial markers only** — it never captures a framebuffer, so there is no pixel
evidence, and it boots via `-kernel`.

### New gate

`scripts/check/check-simpleos-x86-64-wm-host-vulkan-pixel-evidence.shs` (new).
x86_64 rather than aarch64, because `arch/x86_64/gui_entry_desktop.spl` is
already wired to the offload at line 598 and needs no cross-compile:

- boots **OVMF pflash -> GRUB -> multiboot** (never `-kernel`, never
  `isa-debug-exit`), with the argv **self-scanned** immediately before QEMU is
  started, so a later edit cannot reintroduce either flag;
- adds `-object memory-backend-file` + `-device ivshmem-plain` beside the
  firmware chain — the offload transport is orthogonal to boot method, which is
  why the `-kernel` in the existing lane was never actually required;
- captures a real framebuffer via QMP screendump into a PPM;
- asserts real pixel CONTENT by delegating to the existing
  `screen_ppm_distinct_colors.spl` (exit 0 only when >1 distinct colour), so a
  blank or single-colour frame cannot pass;
- labels the renderer **only on a dual receipt**: `renderer=host-vulkan`
  requires the guest's `[wm-frame] host-gpu-ready backend=vulkan` AND
  `host-gpu-presented` AND the host daemon's `HOST_GPU_PROCESS_OK isa=x86_64
  backend=vulkan`. Either side alone, or a daemon that merely started and found
  a device, yields `renderer=cpu`. This matters because
  `gui_entry_desktop.spl:598` passes `backend_required: false`, so the WM
  silently falls back to the CPU rasteriser — a pretty screenshot proves nothing
  about the renderer on its own.

`--selftest` is fatal and runs before anything else. **Measured: `PASS — 12
selftest fixture(s) checked`**, including the two the task required — a
blank/single-colour frame must FAIL, and a device-present-with-`readback_bytes=0`
daemon log must classify as `cpu`, not `host-vulkan` (a direct replay of the
filed `engine2d_vulkan_window_8k` fail-open).

`scripts/check/qmp_screendump.spl` (new) does the QMP turn in pure Simple on the
existing `std.nogc_sync_mut.qemu` client. The older WM lifecycle gate shells out
to `python3` for this (line 110), which the repo's .spl/.shs rule forbids; this
does not copy that.

### Blocker: the host GPU daemon cannot be built from this tree

The gate is ERROR (correctly, fail-closed) because no daemon binary exists. The
`vulkan,cuda,runtime-symbol-table` runtime archive builds green (101,309,322
bytes, 2056 defined `rt_*` symbols), but the daemon link fails:

```
Build failed: 53 runtime symbol(s) referenced by generated code have no
definition in any linked object, runtime archive, or system library:
rt_cpu_arch_name, rt_engine2d_download_pixels, rt_path_normalize, rt_stdin_read,
rt_term_write, rt_string_to_byte_array, rt_vulkan_api_version, rt_webgpu_*, ...
```

These are **not** missing from my link line — they are defined nowhere in the
tree: `grep -rn "fn rt_stdin_read\b|fn rt_vulkan_api_version\b|fn rt_path_normalize\b"`
over `src/compiler_rust/runtime/src/` and `src/runtime/` returns nothing, and
`nm` on the built archive confirms their absence. So
`check-simpleos-qemu-host-gpu-2d.shs` — the one genuinely non-fail-open Vulkan
lane — **cannot currently produce its own daemon on this tree**. Its green
history must predate whatever removed or renamed these symbols.

The documented `SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1` bypass was deliberately NOT
used: it yields a NULL GOT slot per name and a SEGV on first call, which is the
2026-08-21 `rt_unwrap_or_trap` failure mode.

### Compiler gaps hit on the way (both real, both reproducible)

- **Rust seed cannot parse the WM entries.** `gui_entry_desktop.spl:433:17`
  fails with `Unexpected token: expected expression, found Case` on
  `case WmAction.FocusWindow(idx: surface_index):` — enum-variant destructuring.
  The seed is bootstrap-only by rule; noted because it means these lanes require
  a pure-Simple compiler, not just "a compiler".
- **Seed also rejects the daemon:** `semantic: invalid operation: cannot slice
  value of type str with step`.

### Honest status of this objective

| step | status |
|---|---|
| WM already wired to host-Vulkan offload | yes, pre-existing (`gui_entry_desktop.spl:598`) |
| pixel-capturing gate with dual-receipt labelling | **written, selftest green (12 fixtures)** |
| real-firmware boot (OVMF, no `-kernel`) | designed in and argv-enforced; not yet executed |
| host daemon built | **blocked — 53 symbols undefined tree-wide** |
| WM pixels captured | not reached |
| `renderer=host-vulkan` demonstrated | **not demonstrated — and not claimed** |

No framebuffer evidence is claimed for the offload path. The gate exists so that
the claim can be made honestly the moment the daemon builds.

### Scope caveat on the 53-symbol finding

The compiler reports these as "referenced by **generated code**", so the
referenced set is a function of the COMPILER's codegen and its
`RT_OPTIONAL_SYMBOLS` allowlist (`pipeline/native_project/stubs.rs`), not of the
daemon source alone. A different compiler build may reference a smaller or
different set — which is the likeliest explanation for how this lane's
`run_pinned_native_build` (note: *pinned*) ever went green.

What is proven: those 53 names are defined **nowhere in this tree** (`grep` over
`src/compiler_rust/runtime/src/` and `src/runtime/`, plus `nm` on the built
101 MB archive), and the daemon links with **neither** compiler available here.
What is NOT proven: that no compiler can build it. The fix is likely a pinned
compiler, not new runtime symbols.

### Third compiler gap: cranelift verifier rejects f32 icmp_imm

While building `arch/x86_64/gui_entry_desktop.spl`, codegen emitted an integer
compare against an f32 value and cranelift's verifier rejected it:

```
inst130 (v168 = icmp_imm.f32 eq v164, 3): has an invalid controlling type f32
[CODEGEN-STUB-FALLBACK] body compilation failed for 'parse_pct_value':
    ModuleError("Compilation error in 'parse_pct_value': Verifier errors")
```

`icmp_imm` is integer-only; emitting it with an `f32` controlling type is a
backend bug. The build does not abort — it installs a STUB for the affected
function — so an ELF produced this way silently carries non-functional bodies.
That failure mode deserves its own attention independent of this lane.

### Root cause found and FIXED: the offload path's guest half was clobbered, not merely unbuildable

The x86_64 WM ELF build failed on three files. Two were in the host-GPU offload
path itself, and both were missing **declarations**, not missing logic —
casualties of the tree-wipe/merge-restore chain this branch exists to repair
(base: `91b6b9f28dd`, "restore merge-clobbered src/os declarations"):

1. **`struct HostGpuIvshmemDrawIrResult` was declared NOWHERE in `src/`.** It is
   constructed at `host_gpu_ivshmem.spl:291,293,295,299`, returned by
   `host_gpu_ivshmem_submit_draw_ir_retained`, and **exported** at line 344 —
   but `grep -rn "struct HostGpuIvshmemDrawIrResult" src/` returned nothing.
   Hence the compiler's `struct 'ANY' field 'sent_resources'` while lowering
   `Engine2dWmFrameExecutor._render_host_gpu`. Exactly two fields are ever used
   (`receipt`, `sent_resources` — `engine2d_wm_frame_executor.spl:253-254`), and
   the parameter type at line 288 pins the element type, so the restore is
   unambiguous rather than inferred.

2. **`HostGpuIvshmemHelloReceipt.capability_mask` was missing from the struct**
   (11 declared fields) while 2 of its 3 constructors pass `capability_mask: 0`
   (lines 183, 208). The wire protocol independently confirms the field is real:
   `SIMPLEOS_HOST_GPU_WIRE_NEGOTIATED_CAPABILITY_MASK: i64 = 288`, exported from
   `simpleos_host_gpu_protocol.spl:73,416`. The success-path constructor
   (line 210) had also lost its read, so the field was restored **and** wired to
   its protocol offset.

Both restored in `src/os/lib/gpu_bridge/host_gpu_ivshmem.spl`. After the fix the
rebuild shows **zero `hir:`/`codegen:` errors** in the offload path. This is a
restore, not a design change: every element is evidenced by a surviving call
site, export, or protocol constant.

The third failure is the cranelift `icmp_imm.f32` verifier bug in
`dom_color.spl::parse_pct_value` recorded above — unrelated to the offload path,
and NOT worked around with `SIMPLE_ALLOW_STUB_FALLBACK` (which the compiler
itself flags as "unsafe — binary will silently misbehave").

**Consequence for the earlier "53 undefined symbols" finding:** that was the
HOST daemon. This is the GUEST half. They are independent, and the guest half is
now fixed.

### CAVEAT on every build result above: the borrowed compiler read stdlib from ITS OWN tree

After fixing `parse_pct_value` in `src/lib/gc_async_mut/gpu/browser_engine/dom_color.spl`
in THIS worktree, the rebuild reported **the identical error on the identical
function**. The edit was verified present (`parse_pct_value` contains no
`!= nil`), so the compiler was not reading this tree's copy:

| tree | `grep -c "if n != nil"` in dom_color.spl |
|---|---|
| this worktree (edited) | 1 (an unrelated site at line 423) |
| `/mnt/data/worktrees/phase1-rerun` (compiler's own tree) | 3 (the original) |

The count in phase1-rerun matches the error exactly. This is the known hazard
"binary reads stdlib from build worktree": the borrowed Stage-2 compiler lives
under `/mnt/data/worktrees/phase1-rerun/build/...` and resolves `std.*` imports
against **its own** `src/lib`, regardless of this build's `--source src/lib`
(which governs explicit source roots, not stdlib resolution). The fix is to pin
`SIMPLE_LIB="$PWD/src"`, as the admission verifier itself does
(`simpleos-admitted-runtime.shs`: `SIMPLE_LIB="${SIMPLEOS_ADMITTED_RUNTIME_ROOT:-.}/src"`).

**What this does and does not invalidate:**

- **Still valid — the `src/os` restores.** `HostGpuIvshmemDrawIrResult` and
  `capability_mask` live under `src/os`, passed as an explicit `--source` root
  relative to this worktree's cwd, and the errors naming them disappeared after
  the edit (3 failed files -> 1). The declarations were genuinely missing here,
  confirmed independently by `grep -rn "struct HostGpuIvshmemDrawIrResult" src/`
  returning nothing.
- **Still valid — the cranelift `icmp_imm.f32` bug**, which was reproduced on
  standalone fixtures in the scratchpad, not through stdlib resolution.
- **Now DOUBTFUL — the "53 undefined `rt_*` symbols" daemon finding.** That build
  also ran on the borrowed compiler, so the referenced symbol set was computed
  against phase1-rerun's `src/lib` and runtime, not this tree's. The earlier
  caveat ("the referenced set is compiler-dependent") now has a concrete
  mechanism. That finding must be re-measured with `SIMPLE_LIB` pinned before it
  is treated as a property of this tree. The `nm`/`grep` evidence that those
  names are undefined **in this tree** stands; the claim that the daemon
  *requires* them does not.

Operational rule for anyone continuing this lane: **always export
`SIMPLE_LIB="$PWD/src"` when driving a compiler binary that lives in another
worktree**, and re-verify any prior result that did not.

### RETRACTION: the "borrowed compiler read stdlib from its own tree" section above is WRONG

That section inferred a wrong-worktree stdlib read from a `grep -c` coincidence
(1 here vs 3 in `phase1-rerun`). It is incorrect, and is retained above only so
the reasoning error is visible rather than quietly deleted.

Two things disprove it:

1. **The compiler's own error message names THIS worktree's path**, in both the
   before and after runs:
   `/mnt/data/.../agent-a432e642da13971df/src/lib/gc_async_mut/gpu/browser_engine/dom_color.spl`.
   It was reading the edited file all along.
2. The `1 vs 3` count is fully explained without any wrong-tree read: the
   original function contained two `!= nil` sites plus one unrelated site at
   line 423. Removing the two leaves one. `phase1-rerun`'s unedited copy still
   has all three.

**The real cause of the repeat failure was that the workaround itself did not
work** — see the CORRECTION in
`doc/08_tracking/bug/cranelift_optional_float_nil_check_icmp_imm_2026-08-31.md`.
The `icmp_imm.f32` trigger is an optional-float unwrap inside a branch with an
early `return`, so rewriting `!= nil` to `?? 0.0` while keeping the
early-returning shape changed nothing.

**Consequently the doubt cast on the 53-symbol daemon finding is also
withdrawn**: that build was not reading another tree's stdlib either. The
finding reverts to its earlier, weaker-but-honest status — those 53 names are
undefined in this tree, the daemon did not link with either compiler available
here, and the referenced set remains compiler-dependent in principle (the
`RT_OPTIONAL_SYMBOLS` mechanism), but there is no longer any evidence of a
cross-tree artefact.

The operational advice to pin `SIMPLE_LIB="$PWD/src"` when driving a compiler
binary from another worktree is still sound hygiene; it simply was not the
problem here.

### The corrected cranelift fix WORKED; the build now reaches LINK and fails on a stale linker script

With `parse_pct_value` rewritten to the single-tail-unwrap shape, the codegen
failure is gone and the x86_64 WM desktop build advances all the way to the
**link** stage — further than any earlier attempt. It now fails there:

```
ld.lld: error: examples/09_embedded/simple_os/arch/x86_64/linker.ld:127:
    symbol not found: kernel__abi__syscall_shim__spl_handle_mprotect
  ... :128 spl_handle_spawn_binary
  ... :129 spl_handle_ipc_send      ... :130 spl_handle_ipc_recv
  ... :131 spl_handle_ipc_create_port ... :132 spl_handle_ipc_connect
ld.lld: error: too many errors emitted, stopping now
```

**This is a stale contract, not missing code.** All six handlers exist:

| handler | actual module |
|---|---|
| `spl_handle_mprotect`, `spl_handle_spawn_binary` | `src/os/kernel/abi/syscall_shim_process.spl` (lines 286, 307) |
| `spl_handle_ipc_*` (4) | `src/os/kernel/abi/syscall_shim_ipc.spl` (line 29 ff.) |

`linker.ld` aliases **66** symbols through the `kernel__abi__syscall_shim__`
prefix, and only these 6 fail — the rest (`spl_handle_mmap`, `munmap`,
`list_tasks`, `signal`, …) resolve, so they are still in `syscall_shim.spl`.
The six were evidently moved into `syscall_shim_*` submodules by a refactor and
the linker script was never updated; it carries **no** submodule-prefixed
reference anywhere (`grep -o "kernel__abi__syscall_shim_[a-z]*__"` returns
nothing). Note also that all six are declared `fn`, not `pub fn`.

**Deliberately NOT fixed here.** The plausible repair is to repoint those six
lines at the submodule-mangled names (or re-export the handlers from
`syscall_shim.spl`), but `linker.ld` is shared by **every** x86_64 SimpleOS
kernel, so a speculative edit has a far larger blast radius than the two
`src/os` restores above — those merely restored declarations proven missing by
grep. Verifying a linker-script change costs another full ~1 hour build, and
even a successful ELF yields no Vulkan pixels while the host daemon remains
blocked. Whoever picks this up should confirm the submodule mangling convention
first (no example of it exists in this file to copy).

This also means the x86_64 `gui_entry_desktop.spl` kernel has been unbuildable
for some time, independently of anything in this session.

### Final state of the x86_64 WM build chain

| defect | status |
|---|---|
| `HostGpuIvshmemDrawIrResult` declared nowhere | **fixed** |
| `HelloReceipt.capability_mask` missing | **fixed** |
| cranelift `icmp_imm.f32` on early-returning optional-float unwrap | **worked around + filed** |
| `linker.ld` stale syscall-shim aliases (6) | **open, characterised above** |
| host GPU daemon: 53 undefined `rt_*` | **open** |

Four of five understood; two fixed outright. No framebuffer evidence was
produced, and none is claimed.
