# Unbraced renaming re-export resolution

**Status:** implementation handoff; fail-first HIR cases added, no source-matched
runtime result yet. **Scope:** the exact `export use m.orig as local` gap in
`doc/08_tracking/bug/no_renaming_re_export_blocks_zero_cost_facade_alias_2026-09-03.md`.

## Current representation

`parse_use_decl()` in `parser_decls_use.spl` consumes every dotted segment as
one module path. A trailing `as local` becomes one import item encoded as
`whole.module.path:local`. `parse_export_decl()` passes that declaration to
`_export_record_reexport_surface`, which records the same encoded text as the
export. Braced `export use m.{orig as local}` instead records module `m` and
item `orig:local` and is already a distinct working source route. The
unbraced form therefore loses its item boundary before HIR resolution.

The frozen module-surface builder resolves only the full import module path.
If that path is absent, its target index stays invalid; its export route uses
the whole dotted source name. HIR `resolve_import_symbols()` independently
looks up `imp.module` from the parser import, so changing only the frozen
surface index would leave that consumer inconsistent. The interpreter also
tries a selective load for a nonempty import list and therefore never takes
its existing compact `use a.b.member` retry path. These three owners must
agree before either spelling can be admitted.

## Resolution rule

Treat an unbraced dotted rename as an unresolved path until the module
registry is frozen. If the complete path names an admitted module, keep its
module alias meaning. If it does not and its parent path names an admitted
module exporting the final segment, bind the final segment as an item alias
with that parent's canonical declaration, effects, visibility, and ABI. If
neither exists, report one located missing module/item diagnostic. A complete
module wins when both interpretations exist; no directory search order or
ambient sibling symbol may change the winner.

Resolve this once at a shared owner boundary, then publish the chosen module
index, source item, local name, and resolution kind to frozen surface routes.
HIR, interpreter, native emission, and SMF reload must consume that decision,
not independently split the string. Keep the source import spelling for
diagnostics and the canonical origin for symbol identity. Ordinary `use
module as alias` remains a module alias when the complete module exists.

## Admission checks

1. Run the two HIR cases in `resolve_import_symbols_spec.spl`: missing full
   module falls back to a public item, while a present full module retains its
   namespace alias. Compare the item case with braced re-export origin.
2. Add an exact spelling fixture to interpreter, seed, native object/IR, and
   SMF serialization/reload suites. Require one defining symbol and no
   generated forwarding body for the item alias; verify retained effects and
   visibility through a chained facade.
3. Cover missing parent, missing/nonpublic item, duplicate full-module/item
   candidates, relative/absolute paths, alias collision, and stale generation.
   An incomplete or invalid registry walk must fail closed rather than guess.
4. Measure frozen resolution and hot call paths against the existing braced
   spelling. Do not add a per-call resolver or full-registry scan.

The fail-first tests alone do not admit RU-011: source-matched execution and
seed/native/SMF parity remain required.

## 2026-09-27 HIR namespace step

The first implementation candidate handles the complete-module branch in HIR
`resolve_import_symbols()`: its parser-encoded `whole.module:local` item now
registers `local` as a namespace and qualified target declarations when
`whole.module` resolves, without exposing their bare names. It does not
resolve a missing full module to a parent item, publish that choice in frozen
surface routes, or alter interpreter/seed/SMF behavior. This step remains a
draft until the source-matched test and compiler entry-closure checks run.
