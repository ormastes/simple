# Remaining Work Report — Framebuffer + SMF

Date: 2026-04-16

## Current Status

Completed:
- Desktop serial/editor lane is green.
- Real FAT32-backed editor save/readback lane is green.
- Bare desktop framebuffer lane is green.
- Bare framebuffer baseline was refreshed to the deterministic MMIO probe scene.

Still failing:
- `test/system/simpleos_desktop_with_apps_framebuffer_spec.spl`
- `bin/simple test --mode smf --force-rebuild --timeout 90 test/unit/compiler/target_spec_spec.spl`

## Open Blockers

### 1. With-Apps Framebuffer Lane

Symptom:
- The with-apps framebuffer lane no longer fails on QMP transport or pixel compare.
- It now fails before the expected desktop markers, with a fault-only serial stream in the failing run.

Observed facts:
- The lane was aligned back to the non-disk desktop target shape.
- The checked-in with-apps baseline already matches the captured PPM byte-for-byte.
- The preserved failure is therefore no longer a baseline/capture problem.

Likely root cause:
- A boot/runtime fault specific to the with-apps visual lane path, before the normal marker sequence reaches `remote-grouping:ok`.
- This is distinct from the bare framebuffer lane, which now passes.

Primary files:
- `test/system/simpleos_desktop_with_apps_framebuffer_spec.spl`
- `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl`

Repro:
```bash
bin/simple test --timeout 180 test/system/simpleos_desktop_with_apps_framebuffer_spec.spl
```

Next action:
- Capture a fresh failing serial log for the with-apps lane and compare it against the passing bare lane to find the first divergence before `remote-grouping:ok`.

### 2. SMF Test Execution (`std.spec` / `expect`)

Symptom:
- The SMF path got past the earlier `platform` and `target_spec` blockers.
- It still does not complete cleanly through the `std.spec` export/load path.

Observed facts:
- Direct `expect` dependencies were reduced in:
  - `src/lib/nogc_sync_mut/spec.spl`
  - `src/lib/nogc_sync_mut/spec/__init__.spl`
  - `test/unit/compiler/std/nogc_sync_mut/spec/__init__.spl`
- `target_spec` placeholder was replaced with a real pure-Simple implementation in:
  - `src/lib/common/target_spec.spl`
  - `test/unit/compiler/std/common/target_spec.spl`
- Stale checked-in dependency `.smf` fallback was removed from the SMF runner.

Likely root cause:
- The shadow `std.spec` / `nogc_sync_mut.spec` export and SMF loader path still does not present the expected testing symbols consistently during relocation/load.

Primary files:
- `src/lib/nogc_sync_mut/spec.spl`
- `src/lib/nogc_sync_mut/spec/__init__.spl`
- `test/unit/compiler/std/nogc_sync_mut/spec/__init__.spl`
- `src/compiler_rust/driver/src/cli/test_runner/execution.rs`

Repro:
```bash
bin/simple test --mode smf --force-rebuild --timeout 90 test/unit/compiler/target_spec_spec.spl
```

Next action:
- Inspect the final resolved SMF module set for `std.spec` in the shadow `test/unit/compiler/std` tree and verify which symbol owner is expected to export `expect` at load time.

## Suggested TODO Order

1. Fix the with-apps desktop boot fault so the lane reaches `remote-grouping:ok`.
2. Re-run `test/system/simpleos_desktop_with_apps_framebuffer_spec.spl`.
3. Fix the remaining SMF `std.spec` export/load inconsistency.
4. Re-run `bin/simple test --mode smf --force-rebuild --timeout 90 test/unit/compiler/target_spec_spec.spl`.

## Useful Green Reference

Known-good command:
```bash
bin/simple test --timeout 180 test/system/simpleos_desktop_framebuffer_spec.spl
```

This proves:
- QMP screendump transport is working.
- The deterministic MMIO probe scene is visible and capturable.
- The refreshed bare framebuffer baseline is valid.
