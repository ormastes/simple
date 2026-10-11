# SCV native closure leaves re-exported constants undefined

Status: FIXED for the focused native link (2026-10-11); the V4 runtime
regression remains open.

The no-stub, core-C Stage 2 native build of
`test/fixtures/compiler/target6_tracked_move_refresh_probe.spl` selected 66
modules, completed HIR and MIR, and compiled all 66 modules. `ld.lld` then
reported undefined symbols for
`COMPILE_SOURCE_INVENTORY_SCHEMA_V1` and
`COMPILE_SOURCE_INVENTORY_MAX_BYTES_V1`, owned by
`src/lib/scv/compile_source_inventory_core.spl` and re-exported by
`src/lib/scv/compile_source_inventory.spl`. The references came from the
compiled `lib.scv.compile_source_inventory` object. Both constants are
module-level `val` declarations in the core module; the source closure
included both modules. The generated object or link closure needs to provide
their definitions, or consumers need a correct constant lowering path.

Evidence: `build/mini_builds/target6_tracked_move_refresh_probe/build3.log`
in the isolated worktree. Reproduce with the current pure-Simple Stage 2
runtime and `SIMPLE_LIB=src SIMPLE_NO_STUB_FALLBACK=1
SIMPLE_SCV_FREEZE_FALLBACK=1 SIMPLE_SCV_INVENTORY_COLD_INIT=1`, using
`native-build --source src/compiler --source src/app --source src/lib
--source test/fixtures/compiler --entry-closure
--entry test/fixtures/compiler/target6_tracked_move_refresh_probe.spl
--runtime-bundle core-c-bootstrap`.

Expected: link succeeds, then the fixture exits 0 after asserting the final
plugin path is the only selected source. Actual: link fails before runtime.
Three bounded fixture build attempts were used this session; do not repeat
the same check without a concrete linker or lowering repair.

## Repair evidence

Both declarations in `compile_source_inventory_core.spl` are now `pub val`.
The literal private declaration was folded away; the expression private
declaration produced a local `b` symbol, while the facade object referenced
an external definition. A subsequent no-stub Stage 2 build compiled and
linked all 66 selected modules. The corrected fixture then reached SCV
refresh and exposed a separate typed Option guard panic, tracked in
`native_typed_option_none_not_equal_nil_2026-10-11.md`. A complete warm
tracked-move PASS is still required.
