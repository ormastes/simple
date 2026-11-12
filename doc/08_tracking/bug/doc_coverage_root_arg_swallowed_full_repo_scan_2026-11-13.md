# doc-coverage root operand swallowed -> whole-repo scan, no summary (2026-11-13)

Status: fix landed (verification-pending native). Spec: test/01_unit/app/doc_coverage/doc_coverage_root_arg_spec.spl (4/4).

Symptom: `bin/simple doc-coverage src/app/devhub` ran >10 min, printed only compiler diagnostics, no percentage.

Cause: `main()` sliced raw args from fixed index 2; under the dispatch the root operand was dropped, so root defaulted to cwd and the
command printed "Scanning 9253 source files..." (whole repo). A given directory that is not a repo root was also never scanned
(discovery only walks `<root>/src/{std,core,app,lib}` and then narrows to public API).

Fix: `doc_coverage_command_args` slices after the `doc-coverage` token; `discover_directory_files` scans an explicit directory directly;
scanner splits source once per file (`extract_docstring_lines`) instead of once per declaration (quadratic).

Measured (seed, interpreter): 2 devhub files 10.5 s; src/app/devhub (64 files) completes with summary. Residual cost: ~860 lines of
compiler warnings precede the report and the command runs on the interpreter after a JIT HIR failure
(`Cannot infer field type: struct 'Nil' field 'items'` in doc_coverage_command.spl) -- open perf item.

## Follow-up 2026-11-13: JIT HIR fallback fixed (verification-pending native)

Cause: `parse_init_file` (`app/doc_coverage/analysis/init_parser.spl`) held the open group in
`var current_group = nil`, so HIR typed it as struct `Nil` and `current_group.items` failed lowering for every
importer; the per-module JIT reports it against the entry module (`doc_coverage_command.spl`). After a typed
placeholder + `has_group` flag, the next blocker was `PublicApiGroup__create` (the `Type__create` mangled
spelling is an unresolved cross-module symbol under the per-module JIT); all `X__create(` calls in
`app/doc_coverage` now use `X.create(`. `doc-coverage src/app/doc_coverage/types` emits no `[jit-fallback]`.
Spec: test/01_unit/app/doc_coverage/init_parser_group_typed_spec.spl (red 2/3 -> green 3/3).
Measured (seed, JIT): src/app/devhub 64 files 10.1 s; src/app/llm_caret 893 files 13.6 s.

`llm_caret` "11279 items for 58 files": not a defect. 58 is the top-level `*.spl` count; the scan is recursive
(`Scanning 893 source files`, 870 with >=1 item). ~12.9k declaration heads exist under src/app/llm_caret, so
11279 items (~12.6/file) is consistent.
