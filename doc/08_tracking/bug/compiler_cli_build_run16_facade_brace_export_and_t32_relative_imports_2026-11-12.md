# compiler_cli_build run 16: facade `export sibling.{...}` dropped; t32 relative imports unresolved (2026-11-12)

Bootstrap lane `simple-boot-fable-20261112`, release/1.0.0 pin `c7431e08861`,
Stage 2 matrix row `compiler_cli_build` (native-build of
`src/app/cli/_CliMain/main_and_help.spl`, aarch64, cranelift). Failed after
4572 s in phase 3:

```
[collect-all] 37 module(s) poisoned, 95 error(s) collected across 4694 source(s)
```

Log: `build/bootstrap-fable-16/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/compiler_cli_build.log`
(24820 lines). Stage 2 binary sha256 `574c95d29a8dc301…` (stage2-admitted ==
stage2). Runs 13-15 never reached this point (run 13 SEGV in native_compile,
run 14 private-import hard errors, run 15 status 88 at 0 s), so none of the
classes below has a prior green to compare against.

## Class A — FIXED here: `export sibling.{A, B}` in a package facade

Root errors (6 of 95, all in `src/lib/common/diagnostics/__init__.spl`):
`missing module surface for diagnostic_v1 | diagnostic_batch (x2) |
source_position | fix_ranking | fix_transaction`. Cascade: 25x
`unresolved type: LineStartTable` + 1x `unresolved name: LineStartTable`
poisoning `lib.editor.services.*` (18 modules) and `app.editor.*` (4).

Two halves, both now agreeing with the `export A, B from sibling` form:

1. **Parser** (`src/compiler/10.frontend/core/parser_decls_use.spl`,
   `parse_export_decl`, the `export ident.{...}` branch at the old line 245):
   emitted the BARE module `diagnostic_v1`. `parse_export_source_module`
   (line 93) spells a dotless source `.sibling`, and
   `resolve_module_key_relative`
   (`20.hir/hir_lowering/_Items/module_import_registration.spl:1233`) sends a
   dotless name to the absolute resolver only, so the sibling was missed even
   when its surface was committed (log line 13382 `commit-done
   src/lib/common/diagnostics/diagnostic_v1.spl` vs. the error). Fix: a
   dotless module part becomes `.ident`; a dotted one is taken as spelled (`saw_dot` rule)
   (`src/lib/nogc_sync_mut/database/vector/__init__.spl` relies on that).
2. **Entry-closure scanner**
   (`src/compiler/80.driver/driver_entry_closure_core.spl`,
   `_driver_entry_import_module_paths_text_fallback`): followed `export X.*`,
   `export use`, `export ... from M`, never `export X.{...}`; and its
   whole-content early-out admitted only files containing `use `/`import `/
   ` from `. `source_position.spl` is reachable only through the facade and
   has NO phase-2 surface line in the run-16 log (3094 surfaced of 4694).
   Fix: a `.{` export line is collected as `.sibling` (dotted taken as spelled); single-member `export sibling.Name` is followed too
   and `export ` admits the scan.

Cheap repro (6.5 min, run from a fresh worktree, Stage 2 binary above):

```
printf 'use std.common.diagnostics.{LineStartTable}\n\nfn main() -> i64:\n    val t = LineStartTable.build("ab\\ncd")\n    0\n' > build/repro/diag_entry.spl
SIMPLE_FILE_WORKERS=0 SIMPLE_MIR_SHARD_COUNT=8 SIMPLE_SHARD_MEM_CLAMP=1 \
SIMPLE_PARSE_SHARD_WORKER_KB=25165824 SIMPLE_HIR_SHARD_WORKER_KB=9000000 \
SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=29360128 <stage2> native-build \
  build/repro/diag_entry.spl --entry-closure --low-memory --threads 2 \
  --cache-dir build/repro/cache1 -o build/repro/diag_entry.bin
# rc=1: "2 module(s) poisoned, 7 error(s) collected across 3 source(s)";
# all five braced siblings "missing module surface".
```

Spec: `test/01_unit/compiler/bootstrap/entry_closure_export_brace_sibling_spec.spl`
(0/5 before, 5/5 after, seed `bb472edeb8170164…`). Six facades in the tree
use the braced form; this was the first one inside the full-CLI closure.

## Class B — FIXED (2026-11-12): `.x` relative imports in the symlinked t32 app dirs

~60 of the 95 errors: every `use .types.{...}` / `.bridge` / `.render` /
`.commands` / `.cli_shell` / `.error_codes` / `.session` in
`src/app/t32_cli/*` and every `.session_state` / `.session_tools` /
`.json_helpers` / ... in `src/app/mcp_t32/*` report `missing module surface
for .x`. All those files DID get phase-2 surfaces under their alias path
`src/app/t32_cli/...`; the miss is in phase-3 resolution. `src/app/t32_cli`
and `src/app/mcp_t32` are symlinks into `examples/10_tooling/trace32_tools/`.

**Reproducer (run12, ~1 min, same Stage 2 binary `574c95d2...`).** The
matrix row's real argv is built by
`scripts/bootstrap/phase-c-backend-commands.shs` `bootstrap_phase_c_run_tool_build`:
`native-build <entry> --backend=llvm --low-memory --entry-closure --cache-dir ..
--timeout ..` with `SIMPLE_FILE_WORKERS=0 SIMPLE_MIR_SHARD_COUNT=8` -- a
positional entry, NO `--source` roots. That shape takes the in-process
capsule route (`driver:compile:start ... input_files=src/app/cli/<entry>`,
relative), which never admits an SCV snapshot, so the symlinks stay real.
A t32-only probe entry (`use app.t32_cli.mod.{t32_cli_main}`) under
`src/app/cli/` with that argv and the row env gives
`[collect-all] 16 module(s) poisoned, 54 error(s) collected across 236
source(s)`, all 54 `missing module surface for .<sibling>` (mod.spl x20,
cli_shell x15, session_tools x13, action_tools x10, bridge x6, ...) -- the
run-16 shape. The same entry with `--source` roots (coordinator route, SCV
snapshot, symlinked dirs materialised as real dirs) resolves every import.

**Root cause.** `ModuleSurface.canonical_path` is `rt_path_absolute`
(realpath), so for a symlinked facade it is
`.../examples/10_tooling/trace32_tools/t32_cli/mod.spl`; `canonical_name`
is derived from it too (`examples.10_tooling.trace32_tools.t32_cli.mod`),
while the registry key is the lexical `module_name` `app.t32_cli.mod` (the
only spellings in `index_by_name`). Both relative resolvers --
`module_surface_resolve_relative_key` (`module_surface_registry_index.spl`,
feeds the frozen `import_target_names`) and `resolve_module_key_relative`
(`module_import_registration.spl`, phase-3 fallback at
`module_import_resolution.spl:510`) -- derive the sibling key from
`canonical_path` (`examples.10_tooling.trace32_tools.t32_cli.types`), miss,
and RETURN that miss instead of splicing the logical sibling
(`app.t32_cli` + `.types`). The early return is deliberate for the twin-tier
case (2026-10-13, `relative_tier_sibling_owner_spec.spl`), so the fix keeps
it whenever the facade's own realpath-derived spelling IS a registered key
and falls through to the logical splice (from `module_name` / `ctx_name`,
the registered spelling) only for a displaced facade.

Red -> green: `test/01_unit/compiler/hir/symlinked_facade_relative_sibling_spec.spl`
(builds a registry on the tracked symlink with synthetic module text) 0/2
before, 2/2 after; `relative_tier_sibling_owner_spec.spl` 4/4 and
`module_surface_numbered_path_spec.spl` 4/4 unchanged. The Stage 2 binary is
baked from `c7431e088615`, so run12 cannot be re-run green until the next
Stage 2 is built from this source; the spec is the green evidence.

## Class C — FIXED (2026-11-12): `app.mcp_t32.protocol` uses names it never imports

`unresolved name: t32_nl` (x3), `T32_USE_JSON_LINES` (x2), `t32_server_name`,
`rt_file_read_text`, `print_raw` (x2). `t32_nl`/`t32_server_name` are defined
in `examples/10_tooling/trace32_tools/t32_mcp/main.spl` and used from
`protocol.spl` without an import. Reproduces at release/1.0.0 HEAD
(`7c07cde0620`) on the materialised tree: the `app.t32_cli.mod` repro ends
with exactly `1 module(s) poisoned, 8 error(s)`, all in `protocol.spl`.
Source defect in the example tree (introduced by `6889c95ddd6`); independent
of A and B.

**Fix (class C):** `protocol.spl` now owns `T32_USE_JSON_LINES`, `t32_nl`,
`t32_server_name`, `t32_server_version` (main.spl imports them; it cannot be
the owner without a cycle) and declares `extern fn rt_file_read_text` /
`extern fn print_raw` (C runtime symbol, tagged-text ABI). Red→green:
`test/01_unit/app/mcp_t32/mcp_t32_protocol_owned_names_spec.spl` 0/2 → 2/2,
and a Stage 2 `native-build` of a tiny entry importing
`app.mcp_t32.protocol` goes from `1 module(s) poisoned, 8 error(s)` to a
linked binary that emits a framed `initialize` reply.
