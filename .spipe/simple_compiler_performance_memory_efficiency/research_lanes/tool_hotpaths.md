<!-- codex-research -->
# Compiler and tool hot-path audit lane

Scope: static inspection at the worktree revision based on commit `37bd406e219cc35cae049b4130f5167c21801864`. No compiler, tests, or benchmarks were run in this lane. “Measured” below means pre-existing repository evidence; all other cost claims are source-derived risks pending measurement.

## Findings

### 1. Lint reparses each `.spl` input; the parser cost is already measured

- `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:57-68` first runs text lints and then calls `parse_module_silent_checked(content, path)` for every `.spl` file. This API accepts source text, not a cached typed-HIR/MIR artifact.
- Existing measurements in `doc/08_tracking/bug/lint_single_file_superlinear_timeout_on_line_count_2026-08-06.md:215-264` show approximately 0.19–0.20 seconds/line after the fixed floor, with 800-line `.spl` input taking 154.65s versus 4.64s for the same bytes under `.txt`. The report attributes 99.0% of size-dependent lint time to the parse gate plus AST checks and further narrows it to the parser at lines 268-280.
- The same report establishes linear rather than superlinear scaling (`k≈0.9–1.0`) at lines 225-233. Therefore the observed defect is a severe per-line constant and frontend reuse failure, not evidence of parser asymptotic growth.
- Single-file lint does **not** scan the whole tree: `src/app/io/cli_lint_commands.spl:168-178` invokes discovery only for directory targets, matching the explicit source audit in the bug report at lines 389-405.

Candidate bounded baseline (do later): one warm process, synthetic 2/200/400/800-line families, 3 repetitions each, record median parse-gate time, checks-only time, peak RSS, and parser artifact-cache hit/miss. Acceptance target should compare the same native binary and cap marginal Tier-0 lint work at ≤3% after frontend reuse; do not reuse the historical contended absolute times as a release SLA.

### 2. Loop detection rebuilds graph maps per candidate header

- `src/compiler/60.mir_opt/mir_opt/loop_detect.spl:101-130` identifies candidate headers and calls `build_loop_info` once per candidate.
- Each call invokes `reachable_from` and `can_reach_target` at lines 215-216. Those helpers rebuild the complete successor map (`:155-174`) and predecessor map (`:176-197`) from every block.
- Both DFS stacks remove the tail via slicing (`:167`, `:190`), which may copy storage depending on array semantics. The maps are unquestionably rebuilt; slice allocation/copy cost is a derived risk.
- Resulting source-level upper bound is roughly `H * (V + E)` graph construction/traversal for `H` candidate headers, before later per-header block scans at `:221-262`.

Candidate bounded baseline: generated reducible CFGs at 64/128/256/512 blocks with (a) one loop and (b) `H≈V/4` loop headers. Record loop-analysis wall time, allocations/bytes, successor-map builds, predecessor-map builds, and worklist copied elements. Require one CFG/predecessor construction per function and near-linear scaling in `V+E` for a fixed loop density.

### 3. DCE performs per-definition instruction scans and cannot eliminate the no-local-use case

- `src/compiler/60.mir_opt/mir_opt/dce.spl:250-254` calls `is_instruction_result_used` for every instruction.
- That helper scans the block again from its beginning until the subject instruction and then scans later instructions for a use (`:315-339`), producing quadratic block work in the no-use/worst-position family.
- After finding no local or terminator use, it returns `true` conservatively (`:341-346`), so the expensive negative scan does not permit elimination.

Candidate bounded baseline: single blocks with 128/256/512/1024 independent pure definitions and no uses. Record instruction-use predicates, instructions visited, elapsed time, peak temporary bytes, and removals. A rehabilitated implementation should visit instructions/uses linearly and remove all semantically dead pure definitions in the sentinel.

### 4. Vector dependence construction contains pair products and repeated array concatenation

- Def-use collection itself is keyed by local and linear over emitted operand occurrences (`src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl:76-107`).
- Operand extraction repeatedly assigns `uses = uses + get_operand_locals(...)` for binary, aggregate, GEP, and call operands (`:153-198`). This constructs intermediate arrays; exact copy behavior requires runtime measurement.
- Dependence detection explicitly computes every definition × use pair for RAW and WAR (`:222-253`), with an analogous definitions pairing for WAW immediately afterward. For heavily reassigned locals this is quadratic in occurrences and can emit quadratic dependency records.

Candidate bounded baseline: loops containing 64/128/256/512 alternating definitions and uses of one local, plus a many-locals control. Record operand arrays allocated, copied elements, pair comparisons, emitted dependencies, time, and RSS. Set a hard analysis-node/result budget; on exhaustion return a precise “analysis incomplete” remark rather than continuing unbounded.

### 5. CSE and GVN allocate textual expression identities

- CSE converts each expression to interpolated text (`src/compiler/60.mir_opt/mir_opt/cse.spl:56-83`) and uses `Dict<text, LocalId>` (`:105-136`).
- GVN likewise uses `Dict<text, i64>` (`src/compiler/60.mir_opt/mir_opt/gvn.spl:34,61-73`) and creates text for constants and operands/signatures (`:235-238`, `:331-367`).
- This is observed allocation/hashing structure, but its runtime share is unmeasured. Structural interned keys would avoid formatting and make type/flag identity explicit.

Candidate bounded baseline: 1k/4k/16k arithmetic MIR instructions with 0%, 50%, and 90% redundancy. Record key bytes created, key allocations, hash probes, time, and RSS. Compare textual and structural-key variants under identical semantics; require zero text-key construction in the structural implementation.

### 6. Full-tree scans and subprocess boundaries are explicit and partly avoidable

- Directory/project source loading shells out to `find` in `src/compiler/80.driver/driver_source_pipeline_loading.spl:76-90` and `src/compiler/80.driver/driver_source_loading.spl:974-999`, then materializes stdout and splits it into lines.
- Non-entry-closure project builds bulk-load `src/app`, `src/lib`, `src/compiler`, and `src/runtime` at `driver_source_pipeline_loading.spl:286-312`; comments document that indiscriminate bulk loading previously parsed 600+ unrelated modules and exceeded CPU/RSS guards (`:287-292`). Entry closure suppresses this path.
- Lint’s former path deduplication bug is already corrected: `src/app/io/cli_lint_commands.spl:153-178` documents ~32k discovered files, replaces array membership with dictionary-keyed sets, and avoids duplicate targets/files. Treat this as a regression guard, not an open defect.
- Tool/audit scans also launch shell `find` processes, for example `scripts/audit/api_consistency_audit.spl:105-106`, `scripts/audit/diagnostic_catalog_audit.spl:75-76`, and `scripts/audit/repo_hygiene_audit.spl:151-152`. These are cold audit paths, not evidence of compiler request-path cost. Consolidation is useful only if invocation frequency or measured cost warrants it.

Candidate bounded baselines: (1) entry-closure build versus bulk project build: discovered, opened, parsed, and retained source counts plus startup time/RSS; (2) scanner fixture trees of 1k/10k/32k paths: subprocess count, bytes materialized, dedup probes, time/RSS; (3) warm daemon/language-tool requests: assert zero recursive scans and zero compiler subprocesses on hot requests. Use explicit file-count/time/output-byte ceilings and fail closed when exceeded.

## Priority synthesis

1. Reuse parser/typed-HIR artifacts in lint and establish a warm-process parser baseline; this is the only audited item with strong existing runtime attribution.
2. Build cached per-function CFG/predecessor/loop and linear def-use facts; instrument build counts so regressions are falsifiable.
3. Bound vector dependence output/work and replace concatenating operand collection.
4. Replace textual CSE/GVN keys after correctness activation gates exist; current performance impact is unmeasured.
5. Preserve dictionary lint dedup and entry-closure behavior with count-based regression tests. Do not misclassify explicit cold audit scans or single-file lint as whole-tree hot paths.
