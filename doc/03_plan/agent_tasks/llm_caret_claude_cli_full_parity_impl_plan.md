# LLM Caret Claude CLI Full Parity - Exhaustive Implementation Plan

Date: 2026-07-05

## Goal

Implement full Claude CLI parity in `src/app/llm_caret` using the current
`tmp/claude/claude-code-main/src` tree as source evidence. Completion means
every feature, file, class, function, function-like const, type, and interface
row is implemented and tested. No feature row may be skipped.

## Generated Inventories

| Matrix | Purpose |
|---|---|
| `doc/03_plan/trace/llm_caret_claude_cli_full_parity_feature_matrix.tsv` | Every generated feature group with file count, LOC, target capsule, phase, and done gate. |
| `doc/03_plan/trace/llm_caret_claude_cli_full_parity_file_matrix.tsv` | Every Claude source file with target Simple file, target minimum LOC, primary test path, and done gate. |
| `doc/03_plan/trace/llm_caret_claude_cli_full_parity_symbol_matrix.tsv` | Every extracted class/function/type/interface/function-like const with target Simple symbol and test gate. |

Current inventory:

- Claude source files: 1902
- Generated feature rows: 599
- Generated file rows: 1902
- Generated symbol rows: 14119

## Work Allocation

| Lane | Matrix phase | Owner | Review |
|---|---|---|---|
| Core CLI runtime | P1 | primary Codex | highest-capability reviewer |
| Tools and commands | P2 | sidecar candidate | primary Codex merge review |
| Terminal UI | P3 | sidecar candidate | visual/manual review |
| Remote bridge/server | P4 | sidecar candidate | security + protocol review |
| Services/plugins/skills | P5 | sidecar candidate | primary Codex merge review |
| Support utilities/platform | P6 | sidecar candidate | primary Codex merge review |
| Integration shell/audit | P7-P8 | primary Codex | highest-capability reviewer |

## Per-Feature Procedure

1. Select one `feature_id` from the feature matrix.
2. Filter the file matrix by `feature_id`.
3. Create every `target_simple_file` for that feature.
4. For each file row, implement behavior until the target file reaches
   `target_min_loc` and passes its `done_gate`.
5. Filter the symbol matrix by the same `feature_id`.
6. Implement every `planned_simple_symbol`.
7. Add unit specs for each target file.
8. Add one feature-level SSpec under `test/03_system/tools/llm/claude_full/`.
9. Generate `doc/06_spec` for the feature SSpec.
10. Update row status/evidence columns in the matrices.
11. Run the full-parity checker.

## Per-File Procedure

For every row in the file matrix:

1. Read the Claude source file.
2. Identify user-visible behavior, state transitions, errors, permissions, IO,
   cache invalidation, and telemetry.
3. Implement equivalent behavior in the mapped Simple target.
4. Preserve MDSOC+ boundaries; move shared concerns into owner facades instead
   of adding raw runtime shortcuts.
5. Create file-local unit tests.
6. Add system coverage through the feature SSpec.
7. Prove target LOC is greater than or equal to source LOC.

## Per-Symbol Procedure

For every row in the symbol matrix:

1. Implement the `planned_simple_symbol` or an equivalent Simple struct/fn.
2. If a TypeScript type/interface maps to a Simple struct or enum-like tagged
   value, record the exact Simple symbol in the row evidence.
3. Add at least one assertion proving the symbol's behavior or data contract.
4. Do not mark a symbol complete only because the file was created.

## Size Parity Gate

Strict default: each mapped Simple target file must have LOC greater than or
equal to the source file LOC. This is intentionally blunt because the user asked
for same-or-larger mapped files. Do not satisfy this with filler comments. LOC
must come from implemented Simple behavior, tests adjacent to the target module,
or generated compatibility data consumed by the target.

## Final Completion Gate

Full parity is done only when:

- feature matrix has no incomplete rows;
- file matrix has no incomplete rows;
- symbol matrix has no incomplete rows;
- all target Simple files exist;
- all target file LOC values meet target minimum LOC;
- all unit and system tests pass;
- generated manuals report `0 stubs`;
- direct runtime/env guard passes;
- existing compact `llm_caret` provider behavior still passes.
