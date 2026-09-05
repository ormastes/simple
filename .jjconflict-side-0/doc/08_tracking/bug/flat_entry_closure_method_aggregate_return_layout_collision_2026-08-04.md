# Flat entry-closure method aggregate return layout collision

## Status

Blocked after the mandatory three fix/verify cycles on 2026-08-04. Do not
resume this rollout; start a fresh, narrowly scoped compiler session.

## Failure

Pure-Simple `native-build --entry-closure` can project fields from the wrong
aggregate after a cross-module method returns a class or struct. The callee
allocates the declared layout correctly, but the caller reuses a colliding
module-local `SymbolId`. In the SimpleOS GPU daemon this selected offsets from
unrelated classes: `Engine2DReadback.pixels` was read at `+0x38` instead of
`+0`, and `device_identity` at `+0xc8` instead of `+0x18`. Completion evidence
also produced an out-of-bounds `+0x40` projection.

## Root cause

The flat entry-closure path returned before full `HirModule` callable-shape
registration. Its flattened function store does not retain
`HirImpl.method_return_struct_names`, while numeric HIR symbols are local to a
module. MIR then accepted a non-null but unrelated caller-table struct symbol
as authoritative.

## Fix contract

- Pre-register callee-owned impl return names before flat lowering.
- Key method shapes by the emitted owner-qualified callable name.
- Prefer that registered shape over any numeric return symbol.
- Seed call-result field provenance before caller field projection.
- Keep ambiguous bare method names out of the method registry.

## Regression

`test/03_system/compiler/native_cross_module_class_field_layout_regression_spec.spl`
uses inferred method-result locals beside a decoy layout and requires both the
interpreter and native entry-closure executable to print `84`.

## Cycle evidence

All three pure-Simple compiler candidates self-hosted successfully (725
modules, zero compile failures), but the exact native regression remained red:

- Cycle 1: sum printed `42`; split diagnostic printed `instance=42` and a
  garbage static value.
- Cycle 2: callee-table declared return fallback added; sum still printed `42`.
- Cycle 3: flat HIR cache extended with `HirImpl` and exact emitted-name
  registration; sum still printed `42`.

Cycle-2 disassembly showed the instance projection at canonical `+8`, while
the static result used the decoy `wanted` offset `+0x50`. The remaining defect
is therefore in static-call result provenance/key selection after the flat
registry is populated, not allocator layout or instance method transport.

## Fresh narrowed follow-up

A later, explicitly resumed three-cycle audit confirmed the static path more
precisely:

- The current-source v5 bootstrap compiler built successfully, but the exact
  fixture still printed `42`.
- The static unresolved-method path accepts the caller-local numeric return
  `SymbolId` first, records `DecoyLayout`, and later owner-qualified correction
  is fill-only. The new correction makes registered `LayoutMaker.create`
  provenance authoritative for both the MIR return layout and field lookup.
- Rebuilding v6 to verify that correction stopped in phase 4 before producing
  a compiler: `interpreter.spl` reported duplicate qualified dependencies for
  `CompiledSymbolKind` and `BackendKind`, followed by unresolved `Symbol`.

The correction in `method_calls_literals.spl` and
`switch_operators_calls.spl` is therefore **unverified**. A fresh compiler
session must first produce v6 without the backend import conflict, then run the
single regression once. Do not promote the SimpleOS Vulkan daemon or rerun its
QEMU graphics gate until that result is `84`.

## Explicit-provider follow-up

The next fresh session avoided the positional in-process import conflict by
using bounded `--source` roots plus `--entry-closure`. It produced v6, v7, and
v8 pure-Simple bootstrap compilers successfully. Three focused cycles tested:

1. owner-qualified static result provenance;
2. closure-wide qualified field-layout hydration;
3. ambiguity-checked bare field-layout hydration for erased impl metadata.

Every compiler built the regression successfully, but every executable still
printed `42`. The experimental provenance/layout edits were removed because
they did not improve the result. The next session must trace the actual static
result write and field projection at MIR instruction generation (not only the
name registries) before proposing another fix.

## Full-CLI authority audit

The explicit bootstrap builds above delegated through the native provider;
their fixture binaries did not exercise the pure-Simple in-process lowering
path. A fresh audit therefore targeted the required Stage4 full CLI.

- The positional pure-Simple path initially trapped in `lower_class_type`
  because `HirClass.has_export_attr` was true while `export_attr` was nil.
  `lower_class` now explicitly initializes the desugared presence flag.
- After that fix, the small in-process fixture reached MIR and showed that the
  non-flat path loses imported instance/static method ownership, emits
  unresolved-method errors, and has no result provenance. This is distinct
  from the flat provider binary's `DecoyLayout` projection.
- The Stage4 full-CLI build then crashed in `expr_env_mirror_enabled` while
  reading a nil element from a `[bool]` module-global cache slot. Expression
  and statement mirror-mode slots now use the adjacent stable `[i64]` sentinel
  representation.
- A rebuilt bootstrap compiler containing both fixes succeeded, but the final
  Stage4 full-CLI build still segfaulted before producing an artifact. The
  three-cycle cap ended the audit before another debugger run.

The Vulkan QEMU gate still requires a Stage4 full CLI that passes candidate
admission and prints `84` for the regression. Provider-delegated bootstrap
outputs are not substitutes for that evidence.
