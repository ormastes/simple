# arm64 `arm64-desktop-engine2d` lane: registration fixed, media chain still blocked (2026-09-01)

Status: **PARTIALLY FIXED**. Registration (Blocker 1 of
`arm64_wm_vulkan_real_firmware_lane_blocked_2026-09-01.md`) is closed at source
level. Three further, independent, pre-existing blockers were found behind it.

## Fixed here

1. **Scenario registration (the original Blocker 1).**
   `get_arm64_desktop_engine2d_target()` had zero callers.
   `arm64-desktop-engine2d` is now registered in
   `src/os/_QemuRunner/scenario_catalog.spl` (scenario fn + catalog list +
   name-accept + name resolver), resolved in `scenario_disks.spl`, given
   marker fragments / completion acceptance in `scenario_exec.spl`, and given
   its own build predicate `_is_arm64_desktop_engine2d_target` (source roots,
   `SIMPLE_BOOTSTRAP=1`, build timeout) in `os_build_run.spl`.
   `simple os build --scenario=arm64-desktop-engine2d` no longer says
   `unknown scenario`; it now dispatches into the media phase.
   Reproduce spec: `test/01_unit/os/arm64_desktop_engine2d_scenario_registration_spec.spl`
   (RED at parent: `function scenario_arm64_desktop_engine2d not found`,
   2 of 3 failed; GREEN after: 3/3).

2. **`SimpleOsPlatformBuildTarget` was missing three fields that three of its
   own constructor sites pass** — `userland_target`, `userland_abi`,
   `userland_firmware_contract` (x86_64 and i686 in
   `x86_platform_targets.spl:32,208`, riscv64 in
   `platform_target_catalog.spl:417`). A half-landed change; the constructor
   half is present on `origin/main`, the class half never was, so
   `simple os build` failed for EVERY scenario with
   `error: semantic: class SimpleOsPlatformBuildTarget has no field named
   userland_target` — repo-wide, not arm64-specific. Fixed by ADDING the three
   fields (defaulted, so the five constructor sites that do not pass them keep
   constructing); the initializers were deliberately not deleted.

3. **aarch64 sysroot libc did not compile.** `src/os/libc/include/wchar.h:6`
   declared `typedef int wchar_t;` while clang's own `<stddef.h>` (included one
   line above) had already typedef'd it as the target's `unsigned int` —
   `error: typedef redefinition with different types`. So
   `scripts/os/simpleos-sysroot-aarch64.shs` had never produced `crt0.o`.
   Fixed by using `__WCHAR_TYPE__` when the compiler provides it, making the
   redefinition identical (legal in C11). Sysroot now builds clean.

## Still blocked (not fixed here)

4. **No compiler passes the aarch64 `native-build --target` probe.** All four
   tracked stage binaries are reported `skip (failed native-build --target
   probe)`, which is the known stage-binary blocker
   (`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`). The
   runner then falls back to parsing the arm64 server-payload sources with the
   Rust seed, whose parser rejects them:
   - `src/os/userlib/fs.spl:537` — the only multi-line `export a, b,` /
     continuation form in `src/os/`: `expected expression, found Dedent`.
   - `src/os/apps/dbd/dbd.spl` — `expected expression, found Newline`
     (a different shape; the chain is not homogeneous, and an unknown number
     of further files sit behind it).
   Reformatting these sources to appease an outdated seed parser was
   deliberately NOT done — that is normalizing a workaround. The real fix is a
   bootstrap redeploy of a pure-Simple compiler that can `native-build
   --target aarch64-unknown-simpleos`.

   Note the arm64 core runtime archive DOES build once you pass
   `--backend cranelift`:
   `SIMPLE_BINARY=<seed> sh scripts/os/simpleos-core-archive.shs --target
   aarch64-unknown-simpleos --out-dir build/os/simple-core-simpleos-aarch64
   --backend cranelift` -> `parts_built=19 parts_failed=0`. With `llvm`
   (the script default) every part fails with `native backend 'llvm' is not
   available in this build`.

5. **Blocker 2 of the original record is untouched.** The
   AAVMF -> `BOOTAA64.EFI` -> `kernel.elf` `protocol: linux` handover of the
   arm64 desktop kernel is still **unproven** — it could not be reached,
   because no kernel was produced. Do not record it as proven.

## Conflicting specs found (unresolved, no code change made)

`test/01_unit/os/gui_entry_desktop_production_render_contract_spec.spl:140,145`
requires that `runner_targets.spl` / `os_build_run.spl` contain NO reference to
`arch/arm64/wm_entry.spl` (i.e. that `get_arm64_wm_qemu_target()` be repointed
at `gui_entry_desktop.spl`), while
`test/01_unit/os/qemu_runner_extended_spec.spl:301` and
`test/03_system/gui/arm64_wm_qemu_contract_spec.spl:156` assert the opposite —
`target.entry == ".../arm64/wm_entry.spl"`. These cannot both hold.
`src/os/qemu_runner_part2.spl:628` carries a duplicate of the same predicate.
Repointing the shared `arm64-wm-ramfb` lane is NOT required to build the
Engine2D kernel, so it was not done; the conflict is recorded for whoever owns
that lane to settle.

## Gate status after this change

`SIMPLE_BIN=<seed> sh scripts/check/check-simpleos-arm64-wm-vulkan-pixel-evidence.shs`
-> rc **2**, unchanged verdict:
`ERROR — nothing was checked: arm64 desktop/WM kernel missing:
build/os/simpleos_arm64_desktop_engine2d.elf`.
The gate cannot move until blocker 4 is cleared.

## 2026-11-03 explicit media compiler admission repair

The current architecture-neutral server media builder still assigned
`SIMPLE_BUILD_COMPILER` directly when present. This bypassed the canonical
selector's seed identity, release provenance, environment-write and target
capability checks. Automatic selection already used that selector. Route both
explicit and discovered compilers through `simple_compiler_select`; the selector
already honors an explicit choice and rejects it when admission fails.

The focused shell contract is
`test/01_unit/scripts/simpleos_server_payload_compiler_admission_test.shs`. It
copies the real builder and selector into a private fixture root and checks
explicit seed rejection, unsupported-target rejection, and a valid fixture
reaching the missing-sysroot boundary for ARM64, x86_64 and RISC-V. Compiler
fixtures are simulated; no payload compilation or target execution is claimed.
The old bypass fails its seed-refusal assertion.

This repair closes one admission hole, not this composite record. Current
scenario registration, target fields and WCHAR typedef fixes remain present.
An admitted pure-Simple compiler must still produce the ARM64 sysroot/runtime,
server payload and desktop kernel; AAVMF-to-BOOTAA64.EFI-to-kernel handover and
fresh native pixel/input evidence remain unverified. The historical
`arm64-wm-ramfb` versus Engine2D source-contract disagreement also remains a
separate scope decision; this change does not repoint either lane.
