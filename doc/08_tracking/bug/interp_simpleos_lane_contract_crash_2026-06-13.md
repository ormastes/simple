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

### Binding wall — entry sources were deleted in a bulk reorg
The four entry `.spl` files (`arch/arm64/fs_exec_entry.spl`,
`arch/arm32/fs_exec_entry.spl`, `arch/riscv32/smoke_entry.spl`,
`arch/x86_64/fs_test_entry.spl`) plus their linker scripts and boot stubs were
**deleted in commit `de204598bfa`** (2026-06-08, a 238,935-file bulk reorg, blank
message). They are not tracked anywhere in the current tree under any name (only
`riscv64/ssh_live_entry.spl` and `x86_64/green_carrier_probe_entry.spl` survive;
the `arm64/arm32/riscv32` arch dirs no longer exist). The riscv64 fs-exec kernel
already on disk was itself built from a now-deleted `smoke_entry.spl`. Restoring
them means reviving a deleted subsystem across a major reorg (dependencies/module
paths changed) — a separate task, out of scope here.

Consequence: the four `sys_qemu_<arch>_fs_exec_spec.spl` system tests for
arm64/arm32/riscv32/x86_64 correctly classify as `missing-media` (diagnosed RED,
fail-closed) and are NOT flippable to live-pass on this host. riscv64 + x86_32
live-pass. This is the honest live-vs-contract split.

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
