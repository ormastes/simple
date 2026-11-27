# Per-file unit lane: every imported module global fails "missing provider declaration"

- Status: fix-implemented in source (2026-11-21); NOT yet proven on a rebuilt compiler
- Severity: P1 (blocks the default per-file route for any closure that imports a module-level `val`/`const`)
- Found: 2026-11-21 (provisional authority build, 1258-module closure)
- Component: compiler driver, per-file unit pipeline
  (`src/compiler/80.driver/driver_pipeline_lowering.spl`, `driver_mir_physical_owners.spl`)
- Binary: admitted Stage 2 built from `0d8a3269bec`
- Regressed by: `2d0ed4aff59` (2026-11-20)

## Observation

```
[mir-module-failure] module=lib.nogc_async_mut.sosix.host_facade ... first=missing provider declaration for imported global 'lib.nogc_async_mut.sosix.text_boundary::SOSIX_TEXT_BYTE_LIMIT'
MIR lowering error: undefined variable SOSIX_TEXT_BYTE_LIMIT at src/lib/nogc_async_mut/sosix/host_facade.spl:141:31
```

Same shape in `lib.nogc_sync_mut.io.external_file` (`FOREIGN_BYTES_LIMIT`) and
`lib.common.build_manager.codec` (`BUILDER_MEMORY_LIMIT_MAX_V2`, `BUILDER_MAX_INPUTS_V1`).
Nothing is special about these declarations: of the 75 modules that reached MIR
in that run they are the only ones that import a module-level global. A name
scan of the 831-file parse closure finds about 105 importers of such globals.

## Minimal repro (3 files, own git repo, existing Stage 2)

```
# src/lib/common/gp/prov.spl
pub val GP_LIMIT: i64 = 16777216
fn gp_check(n: i64) -> bool:
    n <= GP_LIMIT
export GP_LIMIT, gp_check

# src/lib/common/gp/user.spl
use std.common.gp.prov.{GP_LIMIT, gp_check}
fn gp_room(total: i64) -> i64:
    if gp_check(total):
        return GP_LIMIT - total
    0
export gp_room

# src/app/t/main.spl
use std.common.gp.user.{gp_room}
fn main() -> i64:
    val r = gp_room(5)
    print "room={r}"
    0
```

`simple-bootstrap native-build src/app/t/main.spl --backend llvm --target
x86_64-unknown-linux-gnu --runtime-bundle core-c-bootstrap --runtime-path
<repo>/src/runtime --source src/app --source src/lib --entry-closure --threads 2
--mode one-binary` fails with
`missing provider declaration for imported global 'lib.common.gp.prov::GP_LIMIT'`.

Variants, same binary:

| variant | result |
|---|---|
| `pub val` typed / untyped, private `val` + `export`, one-line or multi-line `use` | all fail |
| `SIMPLE_UNIT_TLDR_IMPORTS=0` (MIR child holds the provider's full HIR, `closure modules=2`) | still fails |
| `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` (no per-file units) | builds, prints `room=16777211` |
| importer calls an accessor `fn gp_limit() -> i64` instead of naming the global | builds, prints `room=16777211` |

`SIMPLE_PHASE_RSS=1` shows the cause directly in the failing child:
`aot:mir_physical_owners logical=5 physical=1` right after
`[unit-tldr] import interface-hir hit path=.../prov.spl`.

## Root cause

`lower_module` binds imported globals from its `providers` argument
(`register_imported_global_bindings`, `50.mir/_MirLowering/provider_globals.spl:127`),
and the driver passes `ctx.mir_feed_modules`. `2d0ed4aff59` changed
`driver_mir_owner_disposition_v1` (`driver_mir_physical_owners.spl:104`) so that a
HELD non-target row of a scoped unit is a `placeholder`; the feed rebuild then
drops it, leaving the feed equal to the unit's targets. Struct/enum layouts and
call origins still resolve because the prescan walks `ctx.hir_modules`, which is
why only globals break: the provider's constants are held but never offered.

## Fix

The feed stays the schedule (targets only). A scoped unit now passes
feed + every other held HIR module, one per canonical owner, as `providers`
(`driver_mir_unit_provider_keys_v1`). Unscoped lanes are unchanged.

## Not verified

The compiler change needs a Stage 2 rebuild to take effect; it has not been run.
The key-selection helper was exercised natively as a standalone copy and has a
spec case in `test/01_unit/compiler/driver/mir_physical_owners_spec.spl`.
