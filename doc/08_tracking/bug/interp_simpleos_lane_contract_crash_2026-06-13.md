# Interpreter crash: simpleos_platform_qemu_smoke_lane / lane-contract field access

- **ID:** interp_simpleos_lane_contract_crash
- **Date:** 2026-06-13
- **Severity:** P1 (blocks interpreter-mode testing of all catalog-lane QEMU scenarios)
- **Status:** workarounds landed 2026-06-13 (interpreter root cause open)

## Two distinct Option-poison sites (both worked around, root cause shared & open)
1. **Platform catalog** (`simpleos_platform_qemu_smoke_lane` etc.) — `Option<SimpleOsPlatformBuildTarget>` unwrap mis-binds. Fixed by index-based accessors (`_simpleos_platform_target_index`, `*_or_smoke`, `*_direct`) so no Option crosses a boundary.
2. **Scenario catalog** (`get_all_scenarios()[i].name` / `for s in get_all_scenarios(): s.name`) — the seed interpreter wraps **elements of an imported `[QemuScenario]` list as Option**, so BOTH index AND for-iteration field-access fail with `'name' on Option`. Neither access pattern helps; a single constructor call (`scenario_arm64_virtio_fat32_smf().name`) is clean. Worked around with a name→constructor dispatch in `scenario_exists`/`scenario_by_name_direct` (qemu_runner_part3.spl) covering all 27 scenarios — `bin/simple os build/run/test --scenario=X` now runs without the Option crash.

Note: `simpleos_platform_targets()[0].name` works while `get_all_scenarios()[0].name` does not, despite both being `-> [class]` — the seed's element-type resolution differs by call site. Root cause remains a Rust-seed interpreter bug (document-don't-patch); not chased further this session.

## Build-feasibility blocker for arm64/arm32/riscv32/x86_64 fs-exec kernels (2026-06-13)
With the scenario Option crash fixed, `os build` now reaches the real walls. The
binding constraint is **missing entry sources**, NOT the backend (verified below).

### Backend verification — cranelift is NOT the blocker (2026-06-13)
The default backend table (`_os_build_backend_for_target`) routes arm/riscv/x86 OS
lanes to `llvm`, and this host's driver lacks the `llvm` feature, so the *default*
path fails at the LLVM-availability check (~20ms): `native backend 'llvm' is not
available in this build; ... use --backend cranelift`. But forcing
`SIMPLE_OS_BUILD_BACKEND=cranelift` was tested for all four arches:

| Arch  | target triple              | cranelift accepts triple? | fails at |
|-------|----------------------------|---------------------------|----------|
| arm64  | aarch64-unknown-none      | YES (past backend stage)  | read entry .spl → ENOENT (~32ms) |
| arm32  | armv7-unknown-none-eabihf | YES                       | read entry .spl → ENOENT (~37ms) |
| riscv32| riscv32-unknown-none      | YES                       | read entry .spl → ENOENT (~42ms) |
| x86_64 | x86_64-unknown-none       | YES                       | read entry .spl → ENOENT (~32ms) |

So cranelift accepts every triple at invocation (no "target not supported"
rejection) and all four then fail identically at `Build failed: failed to read
.../<arch>/<entry>.spl: No such file or directory`. Cranelift codegen for these
freestanding targets could NOT be confirmed because the build never reaches
codegen — there is no source to compile. (The code's own comment warns cranelift
"does not provide i686 or RISC-V freestanding object targets", so riscv32/x86 would
likely still fail at codegen even if sources existed; arm64/arm32 are not in that
exclusion and are unverified.)

### Update 2026-06-13 (later): entry sources ARE present; arm64 BUILDS but does not BOOT
Re-checked: the `arch/` tree (incl. `arm64/fs_exec_entry.spl`, `arm64/boot/baremetal_stubs.c`,
`arm64/boot/crt0.S`, `common/`, `shared/`) is **tracked at HEAD** — 163 files, `git status`
clean. The earlier "deleted in `de204598bfa`, not tracked anywhere" framing was stale
(restored by a parallel session). So the build can now reach codegen.

**arm64 BUILDS to a 1.9MB aarch64 ELF** with `SIMPLE_OS_BUILD_BACKEND=cranelift` +
`SIMPLE_ALLOW_FREESTANDING_STUBS=1` (`build/os/simpleos_arm64_fs_exec.elf`, native-build
OK ~30s). **This proves cranelift CAN codegen+link the arm64 freestanding kernel.**

**But the kernel does NOT boot** — QEMU (`qemu-system-aarch64 -machine virt -cpu cortex-a72`,
loader at 0x40200000) produces **zero serial output** and times out. ELF-symbol root cause:
- Entry `0x40200000` jumps to raw `.text`; the real arm64 C boot stub was **never linked** —
  `nm` shows no `_pl011_init`, no `serial_puts_direct`, no `crt0` (only the Simple kernel
  symbols + `arch__arm64__fs_exec_entry__spl_start` + `_c_start`). So no PL011 init runs.
- `rt_volatile_write_u32` / `rt_load_barrier` / `rt_store_barrier` resolve to **weak no-op
  stubs** (`W` at ~0x4037d6xx) injected by `SIMPLE_ALLOW_FREESTANDING_STUBS=1`. The real
  `...io__volatile_ops__rt_volatile_write_u32__fallback` text bodies are present (`T`) but
  unreferenced — the global binds to the no-op. Every MMIO write is therefore a no-op →
  UART never written → silent timeout.
- arm64 has **no `rt_extras.c`** (only `x86_64/boot/rt_extras.c` exists); that is where x86_64
  gets its non-weak MMIO-intrinsic definitions.

So a *bootable* arm64 kernel needs (a) the boot-stub allowlist wired so `crt0.S` +
`baremetal_stubs.c` compile & link as the entry, and (b) a build WITHOUT freestanding stubs
so `rt_volatile_write_*` bind to the real `_fallback` bodies (or an arm64 `rt_extras.c`). That
is net-new build/linker wiring (Rust `linker.rs` boot-stub discovery or an arm64 boot profile),
**not** a source restore — the working riscv64/x86_32 kernels build without the freestanding
flag because their boot path already wires this; arm64's does not.

Consequence: the four `sys_qemu_<arch>_fs_exec_spec.spl` system tests for
arm64/arm32/riscv32/x86_64 correctly classify as `missing-media`/`boot-fail` (diagnosed RED,
fail-closed) and are NOT flippable to live-pass on this host. riscv64 + x86_32 live-pass.
This is the honest live-vs-contract split.

## Symptom
Calling `simpleos_platform_qemu_smoke_lane("riscv64")` (src/os/port/simpleos_multiplatform_build_part3.spl:174) in interpreter mode kills the process with exit code 248 and no diagnostic. When reached through spec files (e.g. `test/01_unit/os/qemu_runner_protection_acceptance_spec.spl`), it instead surfaces as:

```
semantic: undefined field: unknown property or method 'qemu_smoke_lane' on Option
```

even though the access is guarded by `if val target = simpleos_platform_target_by_name(name):` and `simpleos_platform_target_by_name` demonstrably returns a value (`if val` branch taken, "target found" printed) in the same run.

## Repro
```simple
use os.port.simpleos_multiplatform_build.{simpleos_platform_qemu_smoke_lane, simpleos_platform_target_by_name, simpleos_platform_targets}

fn main():
    val targets = simpleos_platform_targets()
    print "targets: {targets.len()}"          # prints: targets: 6
    if val t = simpleos_platform_target_by_name("riscv64"):
        print "target found"                   # prints
    val lane = simpleos_platform_qemu_smoke_lane("riscv64")
    print "lane name: {lane.name}"             # never reached; process exits 248
main()
```
Run from repo root with `bin/simple run <file>` (file must be inside the repo tree for module resolution). `SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed`.

## Impact
- `test/01_unit/os/qemu_runner_protection_acceptance_spec.spl` fails (3/3) in interpreter mode — pre-existing, NOT caused by 2026-06-13 fs-exec fallback hardening.
- Any spec calling catalog-lane scenario constructors (`scenario_riscv64_hosted`, `scenario_*_virtio_fat32_smf`, `scenario_x64_net_user`, …) cannot run.
- Worked around in `test/01_unit/os/qemu_runner_fs_exec_fallback_acceptance_spec.spl` by testing the name-based predicate `fs_exec_lane_name_rejects_resident_fallback` and using the non-catalog `arm64-wm-ramfb` scenario for end-to-end coverage.

## Hypothesis
`if val` unwrap of an Option returned from a sibling-part module function appears to mis-bind when the Option payload is a large nested struct (`SimpleOsPlatformBuildTarget` containing `SimpleOsLaneContract` fields): subsequent field access sees the Option wrapper ("on Option" semantic error) or the interpreter dies (exit 248) depending on call context. Suspect Option representation/copy path for large struct payloads in the interpreter.

## Workaround (landed 2026-06-13)

Restructured `src/os/port/simpleos_multiplatform_build_part3.spl` to avoid returning `Option<large-struct>` across function boundaries. Added `_simpleos_platform_target_index(name) -> i64` helper (returns -1 when missing); all accessors now do `val idx = _simpleos_platform_target_index(name); if idx >= 0: return simpleos_platform_targets()[idx].<field>` — no Option crossing a call boundary.

New catalog helpers added to avoid `if val Option<SimpleOsLaneContract>` patterns in qemu_runner:
- `simpleos_platform_has_qemu_lane(name, lane_name) -> bool`
- `simpleos_platform_qemu_lane_or_smoke(name, lane_name) -> SimpleOsLaneContract`
- `simpleos_platform_qemu_lane_required_markers(name, lane_name) -> [text]`
- `simpleos_platform_qemu_lane_timeout_ms(name, lane_name) -> i64`
- `simpleos_platform_has_board_lane(name) -> bool`
- `simpleos_platform_board_lane_direct(name) -> SimpleOsLaneContract`

Also fixed `simpleos_platform_arch` in `src/os/qemu_runner_part1.spl` (used same bad pattern) and updated `src/os/qemu_runner_part4.spl` + `src/os/qemu_runner_part5.spl` to use the new catalog helpers.

Regression spec: `test/01_unit/os/port/simpleos_platform_catalog_spec.spl` (10 cases, all green).

The interpreter root cause (Option<large-struct> mis-bind on function return) remains open for a Rust-seed fix.
