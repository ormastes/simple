# riscv64 WM/display closure is unbuildable: `clobber("memory")` is unparseable

- **Filed:** 2026-09-01
- **Arch:** riscv64 (x86_64 and arm64 lanes not investigated here)
- **Status:** FIXED 2026-09-01 for the `clobber` parse defect (option (a),
  parser). The lane is still blocked, but by a DIFFERENT, newly filed defect —
  `deref_assign_after_multiline_call_parsed_as_multiply_2026-09-01.md`.
- **Original status:** OPEN — blocks
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


---

## Resolution 2026-09-01 — and two corrections to the localization above

**The root cause stated above is wrong in a way that matters.** The
parenthesized form does NOT lack clobber support:
`try_parse_asm_constraint` (`asm.rs:281`) already routes the identifier
`clobber` to `parse_asm_kw_constraint` (`asm.rs:339`), which builds an
`AsmConstraint { kind: Clobber, reg_class }`. `parse_paren_clobber_list` (:138)
and `parse_clobber_list` (:540) are the PLURAL prefix form
(`asm volatile clobbers(...) { ... }`) and were never on this path.

Two consequences:

1. **The only defect was the argument spelling.** The `clobber` arm called
   `expect_identifier()`, so `clobber(memory)` parsed fine and
   `clobber("memory")` did not. Verified by fixture, both directions.
2. **`clobbers: vec![]` in `parse_asm_parenthesized` is NOT a discard bug and
   was deliberately left alone.** Parenthesized-form clobbers travel in
   `constraints`, and `hir/lower/stmt_lowering.rs:1271-1283` merges them into
   the same list before the `is_known_asm_clobber` check (:1300). The struct
   field is the carrier for the BRACED form only. Nothing is silently dropped,
   and LLVM is not told "nothing is clobbered".

### Fix taken: (a), parser — `asm.rs` `expect_clobber_name()`

The `clobber` arm now accepts an identifier OR a string literal. Justified from
the spec, not convenience: the design doc
(`doc/05_design/language/language_features/syntax_features/inline_assembly_design.md`)
gives the parenthesized operand form register-name arguments as STRINGS
(`in("rax") arg1`, `clobber_abi("C")`), while the braced form
(`asm_embedded_hal_and_dual_run.md` A.4) spells them as bare identifiers. Before
this fix `clobber` was the only register-name argument in the parenthesized form
that rejected the form's own string spelling. Option (b) was rejected: the 15
call sites are written in a spelling the spec sanctions, so normalizing them
would have papered over the grammar hole, which CLAUDE.md forbids.
`src/compiler/70.backend/backend/x86_asm.spl` (`clobber("eax")` etc.) is a free
beneficiary. Name validation is unchanged and still happens once at HIR
lowering; `memory`, `eax`..`edx` are all already accepted there.

RED/GREEN: three `#[test]`s in `asm.rs`'s test module. Against the parent state
(`expect_identifier`), the two string fixtures FAIL and the bare-identifier one
passes; with the fix all three pass. No `.shs` guard was added — the failure is
a unit-testable parser property and the smoke gate is the integration evidence.

### Where the lane stops now

`sh scripts/os/build-simpleos-riscv64-wm-kernel.shs` no longer fails at
`cpu.spl:150`. It now fails at
`src/os/kernel/arch/riscv64/interrupt.spl:349:24` — `*scheduler = state.scheduler`,
filed separately as
`deref_assign_after_multiline_call_parsed_as_multiply_2026-09-01.md`, which also
records a second defect behind it (MIR cannot lower a deref lvalue at all).

### Also fixed here, from the "second, independent defect" section

* `FramebufferDriver.from_scanout_raw(addr, width, height, pitch, bpp)`
  implemented in `src/os/drivers/framebuffer/fb_driver.spl` — the MMIO-mode
  sibling of `from_boot_info`, for boards that read scanout geometry from
  VirtIO-GPU rather than a Limine `FramebufferInfo`. It was already documented
  as existing by `src/os/services/wm/wm_host_2d_simpleos.spl:21`.
* `gui_entry_desktop.spl`: the duplicate `var input_compositor` and the
  use-before-def of `input_byte` were the SAME two-line leftover
  (`val action = uart_char_to_action(input_byte.to_u64())` +
  `var input_compositor = shell.compositor`), shadowing the `var action` at
  :150 and the `var input_compositor` at :149 and reading `input_byte` 30 lines
  before its `val`. Both lines deleted; the loop body already assigns `action`
  from the real `val input_byte = serial_read_byte()` below.
