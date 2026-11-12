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
