# SCV Core Verification Report - 2026-05-15

## Scope

This pass completed the remaining SCV core hardening item from the plan:
parser lock artifact hashes are now validated as safe `sha256_` object ids
before parser cache paths are constructed.

Production-level SCV features remain planned separately in
`doc/03_plan/agent_tasks/scv.md`.

## Evidence

- `bin/release/simple check src/lib/scv/*.spl src/app/scv/main.spl test/02_integration/app/scv_*.spl test/03_system/app/scv/feature/scv_*.spl test/03_system/app/scv/feature/scv_spec.spl`
  passed for 51 SCV files.
- `bin/release/simple check src/lib/scv/integrity.spl test/02_integration/app/scv_parser_wasm_spec.spl`
  passed.
- `SIMPLE_LIB=src bin/release/simple test test/02_integration/app/scv_parser_wasm_spec.spl --mode=interpreter --clean`
  passed: 12 examples.
- `SIMPLE_LIB=src bin/release/simple test test/02_integration/app/scv_mvp_spec.spl --mode=interpreter --clean`
  passed: 11 examples.
- `SIMPLE_LIB=src bin/release/simple test test/02_integration/app/scv_parser_integrity_spec.spl --mode=interpreter --clean`
  passed: 4 examples.
- `SIMPLE_LIB=src bin/release/simple test test/02_integration/app/scv_storage_safety_spec.spl --mode=interpreter --clean`
  passed: 14 examples.
- `SIMPLE_LIB=src bin/release/simple test test/02_integration/app/scv_tree_object_safety_spec.spl --mode=interpreter --clean`
  passed: 5 examples.
- `SIMPLE_LIB=src bin/release/simple test test/02_integration/app/scv_gates_spec.spl --mode=interpreter --clean`
  passed: 9 examples.
- `SIMPLE_LIB=src bin/release/simple test test/02_integration/app/scv_refs_safety_spec.spl --mode=interpreter --clean`
  passed: 11 examples.
- `SIMPLE_LIB=src bin/release/simple test test/02_integration/app/scv_tree_file_link_safety_spec.spl --mode=interpreter --clean`
  passed: 2 examples.
- `SIMPLE_LIB=src bin/release/simple test test/02_integration/app/scv_diff_spec.spl --mode=interpreter --clean`
  passed: 3 examples.
- `SIMPLE_LIB=src bin/release/simple test test/02_integration/app/scv_merge_spec.spl --mode=interpreter --clean`
  passed: 5 examples.
- `SIMPLE_LIB=src bin/release/simple test test/02_integration/app/scv_public_remote_spec.spl --mode=interpreter --clean`
  passed: 7 examples.
- `SIMPLE_LIB=src bin/release/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`
  passed from cache: 3 examples.
- `bin/release/simple check` over explicit `src/app/mcp/**/*.spl` passed: 26 files.
- `bin/release/simple check` over explicit `src/app/simple_lsp_mcp/**/*.spl` passed: 5 files.
- Stub scan over SCV source, app, tests, specs, and docs had no matches.
- File size guard: largest SCV file is `src/lib/scv/integrity.spl` at 718 lines.

## Warnings

- Directory-form smoke commands such as `bin/release/simple check src/lib`
  are not accepted by this checker build and return "cannot read file: Is a
  directory".
- Re-running the `src/lib` smoke with explicit `.spl` files found unrelated
  pre-existing syntax failures in generated/debug matcher fixtures and
  `src/lib/nogc_async_mut/db/dbfs_engine/ns_btree.spl`. SCV files passed in the
  same run.
- Re-running the `src/compiler` smoke with explicit `.spl` files found
  unrelated pre-existing syntax failures in generated matcher fixtures. SCV did
  not modify compiler files in this slice.

## Status

STATUS: PASS for SCV core.

STATUS: WARN for repository-wide lib/compiler smoke because of unrelated
pre-existing failures outside the SCV change scope.
