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
   dotless module part becomes `.ident`; a dotted one stays absolute
   (`src/lib/nogc_sync_mut/database/vector/__init__.spl` relies on that).
2. **Entry-closure scanner**
   (`src/compiler/80.driver/driver_entry_closure_core.spl`,
   `_driver_entry_import_module_paths_text_fallback`): followed `export X.*`,
   `export use`, `export ... from M`, never `export X.{...}`; and its
   whole-content early-out admitted only files containing `use `/`import `/
   ` from `. `source_position.spl` is reachable only through the facade and
   has NO phase-2 surface line in the run-16 log (3094 surfaced of 4694).
   Fix: a `.{` export line is collected as `.sibling` (dotted stays absolute)
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

## Class B — OPEN: `.x` relative imports in the symlinked t32 app dirs

~60 of the 95 errors: every `use .types.{...}` / `.bridge` / `.render` /
`.commands` / `.cli_shell` / `.error_codes` / `.session` in
`src/app/t32_cli/*` and every `.session_state` / `.session_tools` /
`.json_helpers` / ... in `src/app/mcp_t32/*` report `missing module surface
for .x`, with `unresolved name: t32_validate_identifier` (x9) downstream.
All those files DID get phase-2 surfaces (log lines 290, 1448-1478, 4706)
under their alias path `src/app/t32_cli/...`; the miss is in phase-3
resolution. `src/app/t32_cli` and `src/app/mcp_t32` are symlinks into
`examples/10_tooling/trace32_tools/`.

Evidence that the symlink is the variable: the same `app.t32_cli.mod` entry
native-built with the same Stage 2 binary from a fresh worktree resolves every
`.x` import (0 "missing module surface" across 236 sources) -- but that run
compiled inside an SCV snapshot (`build/scv/snapshots/scv-revision-v2-...`),
which materialises the aliases as copied directories. The matrix compiles the
pinned checkout in place (relative `src/app/...` paths in the log, no
`build/scv/snapshots`), where the symlinks are real. Forcing the in-place
shape from a worktree (`SIMPLE_SCV_SNAPSHOT_ROOT=$PWD`) is refused
(`parse-shard closure authority rejected: snapshot-open-not-owned`), so no
cheap reproducer yet. Leads: the frozen `import_target_names` freeze in
`module_surface_registry_index.spl:550-629` and the physical-path branch of
`resolve_module_key_relative` (`module_import_registration.spl:1233`), which
returns the physical resolution even when it is "" instead of falling through
to the logical `app.t32_cli.types` spelling. Run 13 (`f8ad54b28467`) had the
same symlinks in its closure and passed HIR, so the regression is inside
`f8ad54b28467..c7431e088615`.

## Class C — OPEN: `app.mcp_t32.protocol` uses names it never imports

`unresolved name: t32_nl` (x3), `T32_USE_JSON_LINES` (x2), `t32_server_name`,
`rt_file_read_text`, `print_raw` (x2). `t32_nl`/`t32_server_name` are defined
in `examples/10_tooling/trace32_tools/t32_mcp/main.spl` and used from
`protocol.spl` without an import. Reproduces at release/1.0.0 HEAD
(`7c07cde0620`) on the materialised tree: the `app.t32_cli.mod` repro ends
with exactly `1 module(s) poisoned, 8 error(s)`, all in `protocol.spl`.
Source defect in the example tree (introduced by `6889c95ddd6`); independent
of A and B.
