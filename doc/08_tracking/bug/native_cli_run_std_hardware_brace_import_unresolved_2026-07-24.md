# Native CLI in-process `run`: unresolved brace-imports from `std.hardware.*`

- **Date:** 2026-07-24
- **Severity:** high (breaks `bin/simple run` for hardware probes when seed
  delegation is not taken)
- **Status:** fix-implemented-verification-pending — fixed in source by `4b88aebf00b` (2026-08-21); native CLI not re-run (re-verified 2026-11-07, see below)

## Symptom

With the full self-hosted CLI deployed at
`bin/release/x86_64-unknown-linux-gnu/simple` and a `simple_seed` sibling
present, `bin/simple run test/01_unit/lib/hardware/link_mux/jtag_route_probe.spl`
does NOT delegate to the seed and fails in the native in-process pipeline with
a cascade of:

```
HIR lowering error in test.01_unit.lib.hardware.link_mux.jtag_route_probe:
unresolved name: transport_sim_loopback / tap_create / mux_create / CH_JTAG ...
```

Every name comes from `use std.hardware.link_mux.{mux,jtag_route}.{...}`
brace-imports. The same file passes under the Rust seed (interpreter and JIT):
`SIMPLE_BOOTSTRAP_DRIVER=$PWD/src/compiler_rust/target/bootstrap/simple
bin/simple run <probe>` → `JTAG ROUTE PROBE: ALL PASS`.

## Two distinct defects

1. **Import resolution:** the native in-process HIR path does not resolve
   brace-imports from `std.hardware.link_mux.*` (module → `src/lib/hardware/`
   mapping loss or brace-import binding loss). The seed resolves them fine.
2. **Delegation inconsistency:** a scratch-named copy of the SAME binary
   (`wjob` + `simple_seed` sibling) delegates `run` to the seed automatically,
   but the deployed `bin/release/<triple>/simple` takes the in-process path
   despite `_cli_driver_binary()` (src/app/io/cli_ops.spl:191) finding the
   sibling. The selection point that decides in-process vs seed for `run`
   differs by deploy layout and needs a single, predictable rule.

## Related deploy incident (fixed 2026-07-24)

`bin/release/x86_64-unknown-linux-gnu/simple` had been clobbered by a
compile-only bootstrap binary (`simple-bootstrap 1.0.0-beta`, only `compile`
subcommand; Jul 23 03:41 deploy). Restored from `build/native_probe/simple`
(full CLI, `Simple v1.0.0-beta`) + `simple_seed` sibling from
`src/compiler_rust/target/bootstrap/simple`; clobbered binary kept as
`simple.bootstrap-clobber-bak`.

## Workarounds

- `SIMPLE_BOOTSTRAP_DRIVER=$PWD/src/compiler_rust/target/bootstrap/simple bin/simple run <file>`
- or the scratch pattern: copy CLI to `<scratch>/wjob` + seed to
  `<scratch>/simple_seed`, run `wjob run <file>` (also dodges earlyoom, which
  kills processes named `simple`).

## Fix direction

Root-fix (1) in the pure-Simple HIR import binder (test: the three
`test/01_unit/lib/hardware/link_mux/*_probe.spl` under the native in-process
path). For (2), make `run` delegation depend only on sibling presence, not on
binary location/name.

## Re-verification 2026-11-07 (release/1.0.0 @ 0e56cc6bade) — no longer reproduces

No self-hosted CLI is deployed on this host, so the native binary itself was
not run. Instead the regression spec
`test/01_unit/compiler/hir/std_hardware_brace_import_hir_spec.spl` drives the
same pure-Simple pipeline the in-process `run` uses — the driver's import
scanner/resolver (`_driver_entry_import_module_paths`,
`_driver_resolve_entry_import`), `parse_full_frontend`,
`module_surfaces_from_modules`, `hirlowering_for_module(...).lower_module` —
over the real probe sources, executed by the Rust seed
(`/home/yoon/dev/seed-try-target/release/simple`, sha256 `87693d9e927f9bd5...`).

Findings, per stage:
- scanner: the multi-line `use std.hardware.link_mux.mux.{ ... }` yields
  `[std.hardware.link_mux.frame, std.hardware.link_mux.mux, std.hardware.link_mux.jtag_route]`;
- resolver: each maps to `src/lib/hardware/link_mux/<name>.spl`
  (`driver_entry_closure_core.spl:1369` std.-prefix arm);
- HIR: `resolve_module_key` / `module_surface_resolve_absolute_key` fold
  `std.X` -> `lib.X`, matching the path-derived `lib.hardware.link_mux.*`
  surface keys; `jtag_route_probe`, `mux_probe`, `frame_probe` all lower with
  0 HIR errors.
- negative control (same harness, a misspelled name in a multi-line
  `std.hardware` brace-import that is then called) reports
  `unresolved name: mux_create_misspelled` — so 0 errors on the real probes is
  not vacuous.

`SPEC FILE VERDICT: ... outcome=OK declared>=5 executed=5 passed=5 failed=0`.
There is no red phase: the defect was already fixed in source, so no code was
changed here. The `std.X` -> `lib.X` fold in `resolve_module_key`
(`module_import_registration.spl:1179-1187`) landed in `4b88aebf00b`
(2026-08-21), after this bug was filed — i.e. it was fixed, not absent.

Defect (2) (delegation): `_cli_driver_binary` (`src/app/io/cli_ops.spl:351`)
no longer treats a `simple_seed` sibling as an implicit authority; it delegates
only on an explicit `SIMPLE_BOOTSTRAP_DRIVER` (with the self-exec and
release-wrapper guards) and `SIMPLE_NO_BOOTSTRAP_DELEGATE=1` disables it — one
rule, independent of binary name/location (present since `88aac2ffe28`).

Unverified: the natively compiled CLI was not executed (no deployed binary);
a native-codegen miscompile of the same source would be a separate defect.

Side finding: under the seed interpreter, destructuring a 4-tuple returned
from a fn (`val (a, b, c, d) = f()` where the tuple carries `Dict`s and a
`ModuleSurfacesByName`) failed with `semantic: value is not callable`; the
spec uses a struct return instead.
