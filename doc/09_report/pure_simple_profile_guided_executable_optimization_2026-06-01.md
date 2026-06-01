# Pure Simple Profile-Guided Executable Optimization Verification Report

Date: 2026-06-01

## Command Evidence

- Native smoke:
  `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple src/app/compile/llvm_direct.spl /tmp/simple_pgo_goal_smoke.spl /tmp/simple_pgo_goal_smoke --simple-profile-counters --verbose --clean`
- Result: exit `0`, native binary size `16176` bytes, run exit `0`,
  sidecar line count `6`, native `__simple_profile_counters` symbols `4`.
- Sidecar records: `make_text`, `make_obj`, `make_gpu`, and `main` function
  entry counters.
- `.sprof` conversion:
  `sprof_write_native_counter_profile_file("/tmp/simple_pgo_goal_smoke.sprof",
  "goal-smoke", "smoke", metadata, [11, 3, 2, 19])`
- Result: wrote `4` reloadable profile records.
- Layout bridge:
  `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple src/app/optimize/main.spl /tmp/simple_pgo_goal_smoke --layout-plan --profile=/tmp/simple_pgo_goal_smoke.sprof --manifest=/tmp/simple_pgo_goal_smoke.layout --out=/tmp/simple_pgo_goal_smoke.optimized.layout`
- Result: exit `0`; manifest places `main`, `make_text`, and `make_obj` hot,
  and `make_gpu` cold.

## Performance Evidence

- Profile-load startup baseline with `sprof_loader` imported: `75ms`.
- Profile-load startup with one valid `.sprof` load: `77ms`.
- Profile-load overhead: `2.6%`, under the 5% target.
- Native baseline, best of 1000 process runs: `2252ms`.
- Native profile-counter binary, best of 1000 process runs: `2300ms`.
- Native counter overhead: `2.1%`, under the 3% target.
- Native baseline size: `15952` bytes.
- Native profile-counter size: `16176` bytes.
- Representative full-flow native layout evidence now covers the end-to-end
  chain from generated-C profile counters to runtime snapshot, `.sprof`, layout
  map, native symbol-order file, optimized native rebuild, final `nm -an`
  symbol order, and measured before/after runtime/size.
- Representative evidence:
  - `.sprof` records: `15`
  - profile counts: `dispatch=200`, `parse=20`, `rare=0`
  - final optimized order: `_ZL8dispatchv > _ZL5parsev > _ZL4rarev`
  - non-profile counter symbols: `0`
  - baseline size: `16112` bytes
  - optimized size: `6608` bytes
  - runtime sample: `baseline_ms_50=146`, `optimized_ms_50=147`

## Verification Commands

- `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check src/app/optimize`
  passed `7` files.
- `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check src/app/compile`
  passed `9` files.
- `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check src/app/optimize src/app/compile src/os/baremetal/profile`
  passed `27` files after splitting native counter runtime snapshot helpers
  into `src/app/compile/native_profile_counter_runtime.spl`.
- `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check
  test/system/app/optimize/feature/sprof_loader_spec.spl
  test/system/app/compile/feature/native_profile_counter_spec.spl
  test/system/app/optimize/feature/pure_simple_executable_layout_spec.spl
  test/system/os/baremetal/feature/breakpoint_counter_profile_spec.spl`
  passed `4` files.
- `sprof_loader_spec.spl`: `23` passed.
- `native_profile_counter_spec.spl`: `36` passed.
- `profile_layout_cli_spec.spl`: `11` passed.
- `profile_layout_native_smoke_spec.spl`: `3` passed.
- `native_layout_section_map_spec.spl`: `6` passed.
- `pure_simple_executable_layout_spec.spl`: `16` passed.
- `breakpoint_counter_profile_spec.spl`: `24` passed.
- `breakpoint_counter_probe_image_spec.spl`: `17` passed.
- `breakpoint_counter_target_adapter_spec.spl`: `8` passed.
- `tiered_jit_hotspot_spec.spl`: `51` passed.
- `git diff --check` passed after generated spec EOF cleanup.
- `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
- `sh scripts/install-spipe-dev-command.shs --check` returned `STATUS: PASS
  spipe-dev-command wiring`.
- Maintainability file-size scan: all scoped implementation files are below
  `800` lines; `native_profile_counter.spl` is `567` lines and
  `native_profile_counter_runtime.spl` is `326` lines.
