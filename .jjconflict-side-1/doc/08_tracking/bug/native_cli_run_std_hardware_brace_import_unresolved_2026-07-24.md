# Native CLI in-process `run`: unresolved brace-imports from `std.hardware.*`

- **Date:** 2026-07-24
- **Severity:** high (breaks `bin/simple run` for hardware probes when seed
  delegation is not taken)
- **Status:** open — workaround in place

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
