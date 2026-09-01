# riscv64 WM/display closure is unbuildable: `clobber("memory")` is unparseable

- **Filed:** 2026-09-01
- **Arch:** riscv64 (x86_64 and arm64 lanes not investigated here)
- **Status:** OPEN — blocks
  `scripts/check/check-simpleos-riscv64-wm-render-smoke-opensbi.shs`, which is
  therefore landed ADVISORY (honestly RED).
- **Severity:** blocks the entire riscv64 window-manager lane. Every riscv64
  entry that reaches `os.kernel.arch.riscv64.display` — including the tracked
  production desktop `examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl`
  — pulls in the offending file and cannot be compiled.

## Symptom

```
Build failed: failed to parse src/os/kernel/arch/riscv64/cpu.spl at 150:21
during discovery: Unexpected token: expected identifier,
found FString([Literal("memory")])
```

Reproduced with a FRESHLY BUILT Rust seed (`cargo build --release --bin simple`
in `src/compiler_rust`, built from `origin/main` `e6fe722eeef`), via:

```sh
sh scripts/os/build-simpleos-riscv64-wm-kernel.shs        # rc=1
sh scripts/check/check-simpleos-riscv64-wm-render-smoke-opensbi.shs
# -> ERROR — nothing was checked: WM kernel build failed: ... cpu.spl at 150:21
```

The gate fails CLOSED, as designed: a lane that cannot build evaluates zero
rows, which is an ERROR (exit 2), never a PASS.

## Root cause

`src/os/kernel/arch/riscv64/cpu.spl` writes CSRs with the parenthesized legacy
inline-asm form and a clobber clause, 15 times:

```
    unsafe(capabilities: [inline_asm]):
        asm volatile(
            "csrw sstatus, {operand}",
            operand = in(reg) value,
            clobber("memory")
        )
```

The parser accepts no such thing. In
`src/compiler_rust/parser/src/stmt_parsing/asm.rs`:

* `parse_asm_parenthesized` (line 153) — the function that handles exactly this
  `asm volatile( ... )` form — loops over **string instructions and constraints
  only**, and hardcodes `clobbers: vec![]` in the node it builds. It has no
  clobber clause at all.
* The two functions that *do* parse a clobber list, `parse_clobber_list`
  (line 540, `clobbers[a, b]`) and `parse_paren_clobber_list` (line 138,
  `clobbers(a, b)`), both call `expect_identifier()`. A string literal can
  never satisfy either, and both spell the keyword **`clobbers`**, plural — the
  source spells it `clobber`, singular.

So the source is wrong on three independent axes (singular keyword, string
argument, and a form whose parse path has no clobber support), and the parser
is arguably wrong on one (a memory clobber is not expressible in the
parenthesized form that the rest of this file uses).

**This file has therefore never compiled.** That is the load-bearing finding:
the riscv64 display/compositor/WM stack is not "broken by a recent change", it
has no evidence of ever having been built from this source.

`src/compiler/70.backend/backend/x86_asm.spl` uses the same unparseable
`clobber("...")` form (`"eax"`, `"ebx"`, `"ecx"`, `"edx"`) and is presumably in
the same state; not investigated here, since it is outside this lane.

## Why no existing gate caught it

* `scripts/check/check-rv64-display-smoke-qmp-evidence.shs` boots a
  **prebuilt** `build/os/simpleos_riscv64_display_smoke.elf` and its build step
  is `auto`, so a stale-or-absent artifact does not surface a parse failure as
  such.
* The riscv64 real-firmware lanes that are green
  (`check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`,
  `...-hello-world-...`) never import the display module, so their closure never
  reaches `cpu.spl`.
* `check-simpleos-qemu-rv64-desktop-evidence.ps1` is PowerShell and does not run
  on this host.

## Second, independent defect in the same closure

`examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl` — the
tracked "canonical RV64 production desktop" — additionally:

* calls `FramebufferDriver.from_scanout_raw(...)`, which **exists nowhere in
  `src/`**. `grep -rn from_scanout_raw src/` returns exactly one hit, a doc
  comment in `src/os/services/wm/wm_host_2d_simpleos.spl:21`. There is no such
  constructor in `src/os/drivers/framebuffer/fb_driver.spl`.
* declares `var input_compositor` twice in the same scope and reads
  `input_byte` before the `val input_byte = serial_read_byte()` that defines it.

Both are consistent with the file never having been compiled either. Fixing the
`clobber` defect alone will not make that entry build.

## What is NOT the problem

* Not the two riscv64 freestanding traps from this week. The build never gets
  far enough to link, so neither the `baremetal_stubs.c`-vs-`baremetal_runtime_core.inc.c`
  TU-precedence trap
  (`riscv64_in_guest_dict_values_yields_empty_erased_receiver_2026-09-01.md`)
  nor the `len() == 0` fail-open guard
  (`riscv64_freestanding_len_eq_zero_guard_never_fires_2026-09-01.md`) is
  implicated.
* Not the boot chain. riscv64 SimpleOS boots fine under real OpenSBI v1.4
  `-bios fw_payload`; the interpreter lane is GREEN. The blocker is strictly
  the display/WM dependency closure failing to parse.
* Not a stale seed. The seed was rebuilt from this exact tree first.

## Fix options (not taken here — this lane owns the gate, not the grammar)

1. **Source-only, semantics-losing:** drop the `clobber("memory")` clauses.
   Rejected: a memory clobber on a CSR write is load-bearing; silently removing
   it trades a compile error for a miscompile.
2. **Source-only, semantics-preserving:** rewrite the 15 sites into the braced
   form `asm volatile clobbers(memory) { ... }`, which the parser does support.
   Needs the operand syntax (`operand = in(reg) value`) to be expressible there;
   not verified.
3. **Parser:** teach `parse_asm_parenthesized` a `clobbers(...)` clause, and
   optionally accept string clobber names for parity with Rust/C asm. This is
   the change that makes the existing source's intent expressible, and it
   affects every arch, so it belongs to a compiler lane rather than this one.

Whichever is chosen, the check is mechanical: after the fix,
`sh scripts/check/check-simpleos-riscv64-wm-render-smoke-opensbi.shs` must stop
saying `ERROR — nothing was checked` and produce a real PASS or FAIL. Promote
the gate from ADVISORY to MANDATORY once it is green.

## On Vulkan, recorded here so the goal is not overstated

There is **no in-guest Vulkan on riscv64**, and none is blocked by this bug —
it does not exist. The riscv64 WM path produces pixels by Engine2D CPU/SIMD
rasterisation in S-mode and pushes them to the display with VirtIO-GPU
transfer+flush; `gui_entry_desktop.spl` says so itself on serial
(`[backend-evidence] present=virtio-gpu-transfer+flush source=shared-wm-draw-ir-engine2d`).
`src/os/kernel/ipc/host_gpu_ivshmem_map` is a HOST-side offload protocol reached
over an ivshmem BAR (and its declared backend constant is
`SIMPLEOS_HOST_GPU_BACKEND_METAL`), not a guest Vulkan driver. This host does
have working Vulkan 1.4 on two NVIDIA GPUs, but that is host-side and the guest
cannot reach it under this gate's argv. The new gate therefore parses the
guest's own `backend=` line and re-states it verbatim in its verdict, so the
word "vulkan" can only ever appear as `vulkan=absent-in-guest` until a real
guest backend lands and changes what the guest reports.
