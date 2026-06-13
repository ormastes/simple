# Interpreter crash: simpleos_platform_qemu_smoke_lane / lane-contract field access

- **ID:** interp_simpleos_lane_contract_crash
- **Date:** 2026-06-13
- **Severity:** P1 (blocks interpreter-mode testing of all catalog-lane QEMU scenarios)
- **Status:** workaround landed 2026-06-13 (interpreter root cause open)

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
