# Lane TESTDUP — stale duplicate spec tree survey

**Status: STOPPED BEFORE DELETION.** The mirror tree is load-bearing. Nothing was
deleted, moved, or edited. Reversing the migration direction is a user decision.

## 1. Survey (disk state, 2026-07-27)

Mirror tree = `test/unit`, `test/integration`, `test/system` (12,716 files).
Numbered tree = `test/01_unit`, `test/02_integration`, `test/03_system` (21,723 files).

Pairing each mirror file against its numbered counterpart at the same relative path:

| Class | Files | of which `.spl` | of which `.txt` |
|---|---:|---:|---:|
| IDENTICAL | 8,775 | 5,048 | 3,702 |
| DIFFER (diverged) | 1,018 | 1,017 | 0 |
| ORPHAN (mirror only) | 2,923 | 1,617 | 1,293 |
| **Total** | **12,716** | **7,682** | **4,995** |

Raw data: `build/testdup_survey/pairs.tsv`, `differ_sizes.tsv`,
`orphan_true.txt`, `orphan_relocated.txt`, `lasttouch.tsv`, `pathrefs_real.txt`.

### 1a. The `.txt` files are not specs
~5,000 `.txt` are committed, stale, generated run artifacts —
`test/**/<spec_name>/summary.txt` containing Windows paths
(`spec: C:\Users\ormas\dev\simple\test\unit\...`, `duration_ms: 0`). They are junk
in **both** trees, not evidence of spec duplication. Separate cleanup item.

### 1b. DIFFER magnitude (`.spl` only, 1,017 pairs)
| diff lines | pairs |
|---|---:|
| ≤2 | 133 |
| 3–10 | 229 |
| 11–50 | 404 |
| >50 | 251 |

**655 pairs diverge by >10 lines.** These are DIVERGED, not STALE. Largest:
`web/browser_session_fetch_wasm_chain_spec.spl` (6,305), `isel_riscv32_spec.spl`
(1,468), `isel_riscv64_spec.spl` (1,456), `formatter_comprehensive_spec.spl`
(1,039), `simple_web_renderer_spec.spl` (978), `wm_scene_spec.spl` (930).
By tree, >50-line divergence: unit 210, system 23, integration 18.

### 1c. ORPHAN breakdown (`.spl`, 1,617)
- **1,592 relocated**, not orphaned — same basename exists elsewhere in the
  numbered tree (the numbered tree reorganized subdirectory layout). Sampled 200:
  **200/200 byte-identical** to their relocated numbered home. Safe class.
- **25 true orphans** — no same-named file anywhere in the numbered tree. These
  are the only copy of their coverage:
  - `test/unit/compiler/verification/*_spec.spl` (16 files: cache_correctness,
    deterministic_emission, lean_basic, lean_block_integration, lean_codegen,
    lean_workflow, memory_capabilities, naming, proof_reference, regeneration,
    report_rendering, tool_checker, toolchain_detection, unified_attrs,
    unsupported_construct, verification_diagnostics)
  - `test/unit/compiler/parser_gap_array_repeat_mut_param_spec.spl`
  - `test/system/coverage/*_spec.spl` (6: coverage_build, coverage_check_api,
    coverage_core, coverage_doc_stats, coverage_runtime_ffi, coverage_test_runner)
  - `test/system/database/server/db_server_tier_spec.spl`
  - `test/integration/app/.simple_result_1784360140542040_app_mcp_intensive_spec.spl`
    (leaked runner temp file — the one genuinely deletable orphan)

## 2. Which hierarchy is canonical

**Numbered tree is canonical by maintenance. Mirror tree is canonical by runner
semantics. They disagree — that is the whole problem.**

Maintenance evidence (numbered wins):
- Distinct commits touching each tree, last 30 days: **numbered 2,760 vs mirror 128** (21x).
- Mirror `.spl` mtimes: 6,540 of 7,605 frozen at 2026-07-01 (tree creation date,
  `97a9358145f`); numbered tree is spread across June–July with 319 files touched today.
- Cited example confirmed: `test/unit/os/services/pm_service/pm_service_spec.spl`
  is 9,449 B last touched Jul 1; `test/01_unit/.../pm_service_spec.spl` is
  15,472 B touched Jul 27.

Runner evidence (mirror is load-bearing — this is the blocker):
- Default root is `test/` and discovery is an **unfiltered recursive walk**, so
  **both trees are discovered and both are run**:
  - `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:491` — `path = "test/"`
  - `src/lib/nogc_sync_mut/test_runner/test_runner_files.spl:297` — `dirs = ["test/"]`
  - `test_runner_files.spl:326` `dir_walk(base_path)` / `test_manifest_scanner.spl:29,63`
    `dir_walk_native(dir)` → `rt_dir_walk` (`src/runtime/runtime.c:1666`), no name filtering.
  - Selection is filename-only: `test_runner_files.spl:67` — `_spec.` / `_test.`
  - No tree-level exclusion list anywhere.
  - **Deleting the mirror therefore removes ~7,550 spec files from the default run.**
- **Level filters only match the MIRROR tree.** `matches_level`
  (`test_runner_files.spl:91-100`) and `detect_test_level`
  (`test_manifest_scanner.spl:165-174`) test `path.contains("/unit/")`,
  `"/integration/"`, `"/system/"`. The string `/unit/` does **not** occur in
  `test/01_unit/` (it is `/01_unit/`). So the numbered tree scores level 0
  (unknown) and is **excluded from `--unit` / `--integration` / `--system` runs**.
  Deleting the mirror makes every level-filtered run match zero specs.
- `config/simple.test.sdn:6-8` names `unit_dir: test/unit`,
  `integration_dir: test/integration`, `system_dir: test/system`. These keys have
  no reader in the runner (dead), but they document the mirror as the declared layout.
- `src/app/doc/gen_spec_docs.spl:108-130` builds `"{test_dir}/system"`,
  `/integration`, `/unit` — **live** consumer of the mirror paths for spec-doc generation.

## 3. What was removed

**Nothing.** Per the lane's scope-discipline clause, the survey shows the mirror
is genuinely load-bearing, so deletion is escalated rather than executed. See §5.

## 4. Path-reference sweep (performed, not applied)

`grep` over `src/**`, `scripts/**`, `.claude/**`, `config/**` for literal
`test/unit/`, `test/integration/`, `test/system/`: 57,574 raw hits, but 57,524 are
inside `.claude/worktrees/*/doc/TODO.md` copies. **50 real referencing lines:**
- `src/app/doc/gen_spec_docs.spl:108-130` — live doc-generation roots (must be fixed first)
- `config/simple.test.sdn:6-8` — declared dir layout (dead keys)
- `src/compiler/35.semantics/lint_cross_ref.spl` — 3 lines
- `scripts/check/check-llm-tooling-public-absence-rendering.shs` — 4 lines
- remainder are generated artifacts (`src/compiler_rust/doc/test/test_db.sdn`,
  `build/test-artifacts/**`, vscode-test vendor `package.json`)

Full list: `build/testdup_survey/pathrefs_real.txt`.

## 5. Recommended sequencing (needs user decision)

The dedup is safe only after the runner is taught the numbered layout. Order:
1. Fix `matches_level` + `detect_test_level` to match `/01_unit/`, `/02_integration/`,
   `/03_system/` (also `00_formal_verification`, `04_smoke`…`09_baselines`). Until
   then the mirror is the only level-addressable tree. **`src/**` — not this lane's scope.**
2. Repoint `src/app/doc/gen_spec_docs.spl` and `config/simple.test.sdn` at the numbered roots.
3. Then delete the safe classes: 5,048 IDENTICAL `.spl` + 1,592 relocated-and-identical
   `.spl` (~6,640 files) plus ~5,000 stale `summary.txt` in both trees.
4. Migrate the 24 true orphans (verification/, coverage/, db_server_tier,
   parser_gap) into the numbered tree; delete the 1 leaked `.simple_result_*` temp.
5. Merge the 655 substantively DIVERGED pairs by hand — the real cost, and the
   reason a bulk delete would destroy work.

Projected once unblocked: ~11,600 files / est. >1M lines removed. **Actual removed
this lane: 0 files, 0 lines.**

## 5b. Spec verdicts (baseline — nothing was changed, so these are pre-existing)

| Spec | Verdict |
|---|---|
| `test/01_unit/os/arch/duplicate_owner_spec.spl` | **GREEN** 1 example 0 failures; + ledger-parity 2/0 |
| `test/01_unit/lib/common/arch_spec.spl` | **GREEN** 27 examples, 0 failures |
| `test/01_unit/os/services/pm_service/pm_service_spec.spl` | **GREEN** 3 examples, 0 failures |
| `test/02_integration/app/add_remove_log_modes_spec.spl` | **GREEN** 8 examples, 0 failures |
| `test/02_integration/app/cli_dispatch_spec.spl` | **RED** 6 examples, 3 failures — pre-existing (`expected nil to equal false`); numbered-only, no mirror copy exists |
| `test/03_system/net_connect_completion_spec.spl` | **RED** 4 examples, 1 failure — pre-existing |
| `test/unit/compiler/verification/naming_spec.spl` (mirror ORPHAN) | **GREEN** 9 examples, 0 failures — **and has no numbered counterpart** |

The last row is the decisive evidence: a mirror-only spec that passes today. Bulk
deletion of the mirror would have silently destroyed 24 such live specs.

## 6. Deferred (other live lanes)
- `test/01_unit/lib/ecs/**`, `test/unit/lib/ecs/**` — lane ECSGEN
- `test/01_unit/os/services/llm/**` — excluded
- 6 pair rows fall in these paths and were left unclassified for action.
