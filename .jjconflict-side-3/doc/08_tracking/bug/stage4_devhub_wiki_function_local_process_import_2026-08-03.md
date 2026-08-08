# Stage 4 devhub wiki function-local process import

Status: fixed (2026-08-03)
Severity: P1 bootstrap blocker
Fix owner: `/root` — CLAIMED and fixed; do not duplicate

## Reproduction

The x86 Stage 4 full CLI closure passed all 1,431 module surfaces and the prior
database facade failure, then stopped during HIR lowering:

```text
app.devhub.cmd_wiki: unresolved name: process_run
```

`cmd_wiki.spl` placed the same `process_run` import inside each of its two
editor helper functions. The bootstrap parser deliberately consumes a
function-local `use` as a no-op statement, so those imports never register a
HIR symbol.

## Fix

Hoist `process_run`, `storage_to_markdown`, and `resolve_editor` to module scope
and remove every misleading function-local import in the module, including an
unused `env_get`. No compiler fallback or concrete runtime primitive is added.

## Verification

- `test/03_system/native/devhub_wiki_help_import_scope.spl` imports the real
  module and calls its side-effect-free help path, forcing the complete module
  through native HIR lowering without launching an editor.
- A pure-Simple Stage 3 exact `compile cmd_wiki.spl --format=smf` crossed
  `app.devhub.cmd_wiki` HIR after the repair and continued into separately
  unresolved `adapter_confluence` JSON facade names; no `cmd_wiki` diagnostic
  remained.
- The retained-cache full Stage 4 retry is the authoritative closure gate.

The broader language-design gap—function-local `use` parses successfully but
has no semantic effect—remains documented by the parser's explicit no-op and
must be addressed separately from this bootstrap-blocking application repair.
