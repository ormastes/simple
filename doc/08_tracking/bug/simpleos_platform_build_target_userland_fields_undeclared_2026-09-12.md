# `SimpleOsPlatformBuildTarget` never declared the three `userland_*` fields its catalog passes

Date: 2026-09-12
- Status: RESOLVED (2026-09-12) — `src/os/port/_SimpleosMultiplatformBuild/build_target_contracts.spl`; the accessor half is filed separately below and stays OPEN

Binary for every verdict below: `bin/simple` = the shared clone's Rust seed,
`sha256 3d120a6f…`, aarch64 host.

## Summary

`class SimpleOsPlatformBuildTarget`
(`src/os/port/_SimpleosMultiplatformBuild/build_target_contracts.spl:71`)
declared 40 fields, none of them `userland_target`, `userland_abi` or
`userland_firmware_contract` — while **three** of the eight catalog entries
(`riscv64-starfive-jh7110`, `x86_64-simpleos`, `i686-simpleos`) passed exactly
those three named arguments to the constructor.

A named argument that does not name a field is a hard semantic error, and this
one sits in `simpleos_platform_targets()` — the single catalog every accessor
reads — so it did not degrade anything, it killed the whole module:

```
$ bin/simple run src/app/os/main.spl targets
Supported SimpleOS architectures:
error: semantic: class `SimpleOsPlatformBuildTarget` has no field named `userland_target`
```

`simple os targets`, a user-facing CLI surface, printed its header and then
died. Two unit specs were 100% red for the same reason:

```
test/01_unit/os/port/simpleos_platform_catalog_spec.spl   declared>=13 executed=13 passed=0  failed=13
test/01_unit/os/port/simpleos_multiplatform_build_spec.spl declared>=24 executed=24 passed=0  failed=24
```

## Fix

Declared the three fields, with defaults, so the five catalog entries that
stage no hosted userland keep constructing unchanged: `userland_target: text =
""`, `userland_abi: text = ""`, `userland_firmware_contract:
SimpleOsFirmwareContractKind = SimpleOsFirmwareContractKind.BareMetal`
(the enum has no `None`; `BareMetal` is the honest "no userland firmware
handoff" value). No catalog entry and no accessor was changed.

```
test/01_unit/os/port/simpleos_platform_catalog_spec.spl   outcome=OK  executed=13 passed=13 failed=0
test/01_unit/os/port/simpleos_multiplatform_build_spec.spl            executed=24 passed=16 failed=8
$ bin/simple run src/app/os/main.spl targets
  x86_64  ->  x86_64-unknown-none  (qemu-system-x86_64)
  x86_32  ->  i686-unknown-none  (qemu-system-i386)
  riscv64  ->  riscv64-unknown-none  (qemu-system-riscv64)
```

## Still OPEN — the accessor half of the same landed-half change

`simpleos_multiplatform_build_spec.spl`'s remaining 8 failures are **not** this
defect. Three of them are the other half of the same incomplete change:
`simpleos_platform_userland_target`, `simpleos_platform_userland_abi` and
`simpleos_platform_userland_firmware_contract` (plus the short forms
`simpleos_userland_*` the spec calls WITHOUT importing them) do not exist
anywhere in `src/`, and the `aarch64-simpleos` / `armv7-simpleos` /
`riscv64gc-simpleos` / `riscv32imac-simpleos` catalog entries carry no
`userland_*` values, so writing the accessors alone would return `""` for the
`arm64` and `riscv64` cases the spec asserts. The canonical values already
exist as constants in
`src/lib/common/contracts/execution/simpleos_target_v1.spl`
(`aarch64-unknown-simpleos`/`aapcs64`/`RawLoader`,
`riscv64gc-unknown-simpleos`/`lp64d`/`OpenSbi`), so completing it is
mechanical; it was left out of this commit deliberately rather than guessed at,
because the spec's own short-form calls are un-imported and may indicate a
second intended module.

The other 5 failures are unrelated catalog-content drift (artifact-name count
8 vs 6, `xck26-ml-carrier` vs `mlk_s02_100t`, x86 lane naming, riscv fpga
bundle path, Unicode scalar constructor text).
