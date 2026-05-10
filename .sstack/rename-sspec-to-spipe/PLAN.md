# Plan: Rename `sspec` → `spipe` (skill + docs + source + tests)

> **Status:** Phase 1 (dev/refine) complete, awaiting user green-light to start Wave 1.
> **Created:** 2026-04-26
> **Owner:** /dev (sstack alias) on `main`
> **Restart anchor:** Read this file + `.sstack/rename-sspec-to-spipe/state.md` and resume from "Resume Procedure" section.

---

## 1. Goal

User confirmation, verbatim: **"merge them make spipe. rename too"**

Concrete interpretation:
1. **Merge** the four primary `sspec` skill+doc artifacts into one consolidated home at `doc/00_llm_process/spipe/` with a thin `.claude/skills/spipe.md` entry-point.
2. **Rename** every `sspec` reference across the repo (skill harness, source, MCP tool, test fixtures, file extension `.sspec` → `.spipe`, in-file strings/comments).
3. **Keep** historical reports under `doc/09_report/` with their original dated filenames (incident record); only update forward-looking pointers.

Naming meaning (default if user doesn't override): **SPipe = "Simple Pipe", the spec→test→report pipeline.**

---

## 2. Inventory (snapshot, top-level only — `.claude/worktrees/`, `build/`, `target/` excluded)

### 2.1 Files matching `*sspec*` by name (51 files)

**Skill harness (4):**
- `.claude/skills/sspec_loop.md`
- `.claude/skills/lib/sspec.md`
- `.claude/templates/sspec_template.spl`
- `tools/claude-plugin/sstack-lang/skills/sspec_loop.md` (mirror)

**Doc — merge candidates (2):**
- `doc/05_design/sspec_lint_rules_design.md`
- `doc/06_spec/app/compiler/sspec_guide.md`

**Doc — historical record, KEEP filenames (32):**
- `doc/09_report/2026/01/sspec_*.md` × 7
- `doc/09_report/2026/02/*sspec*.md` × 2
- `doc/09_report/misc/sspec_*.md` × 23

**Doc — dashboard (1):**
- `doc/10_metrics/dashboard/tables/sspec_tests.sdn` → `spipe_tests.sdn`

**Source code (6):**
- `src/lib/nogc_sync_mut/sspec.spl` + `.smf` → `spipe.spl/.smf`
- `src/compiler/60.mir_opt/optimization_passes.sspec` → `.spipe`
- `src/compiler_rust/compiler/src/lint/checker_sspec.rs` → `checker_spipe.rs`
- `src/compiler_rust/driver/src/cli/migrate/sspec.rs` → `migrate/spipe.rs`
- `src/compiler_rust/lib/std/src/spec/sspec_docgen.spl` → `spipe_docgen.spl`
- `src/compiler_rust/lib/std/src/tooling/dashboard/collectors/sspec_collector.spl` → `spipe_collector.spl`

**Auto-generated test fixtures (35) — `.sspec_wrapped_entry_*` from generator:**
- Generator location: `src/compiler_rust/driver/src/cli/test_runner/execution.rs`
- Strategy: change generator prefix; delete old fixtures; let test pipeline regenerate.

**Examples — regenerate from renamed source (3):**
- `examples/09_embedded/baremetal/baremetal/hello_riscv32_sspec.elf`
- `examples/09_embedded/baremetal/baremetal/hello_riscv32_sspec.s`
- `examples/09_embedded/baremetal/baremetal/riscv32_test/sspec_baremetal.h`

**Hand-written test specs (2):**
- `test/integration/app/sspec_quality_lint_spec.spl` → `spipe_quality_lint_spec.spl`
- `test/unit/compiler/backend/sspec_system_test_spec.spl` → `spipe_system_test_spec.spl`

### 2.2 In-file string references (counts by top-level dir)

| Files w/ `sspec` strings | Dir |
|---:|---|
| 357 | `doc/06_spec/` |
| 285 | `doc/09_report/` (historical — narrative refs may be kept/updated case-by-case) |
| 143 | `test/unit/` |
| 138 | `src/compiler_rust/` |
|  95 | `test/lib/` |
|  52 | `test/system/` |
|  39 | `test/integration/` |
|  34 | `test/app/` |
|  29 | `src/lib/` |
|  29 | `src/app/` |
|  26 | `doc/05_design/` |
|  25 | `doc/01_research/` |
|  20 | `doc/00_llm_process/` |
|  18 | `examples/nvfs/` |
|  17 | `test/feature/` |
|  17 | `src/compiler/` |
|  16 | `doc/08_tracking/` |
|  16 | `doc/07_guide/` |
| ... | ... |

**Approx total:** ~1500+ files contain `sspec`/`SSpec`/`SSPEC` strings (vast majority are auto-generated wrapped-entry stubs and cascading generated headers; once generator + a few canonical sources are fixed, most disappear by regeneration).

### 2.3 sstack/dev skill cross-refs (4 lines in 1 file)

```
.claude/skills/sstack.md:37  | 4 | spec | QA Lead | … | `/sspec` |
.claude/skills/sstack.md:83  …Claude-native skills only (`/sspec`, …)
.claude/skills/sstack.md:243 - Phase 4 (spec): `/sspec` for test structure
.claude/skills/sstack.md:254 …shares skill references (`/coding`, `/sspec`, …)
```
`/dev` aliases to `/sstack` so updating sstack.md cascades.

### 2.4 MCP / build wiring

- `.mcp.json` — **no `sspec` text** (server name `simple-mcp` is generic; tools dispatch by inner table).
- MCP tool `simple_sspec_docgen` is mapped inside the simple-mcp dispatch table (find it in `src/compiler_rust/.../mcp/` or `src/lib/nogc_sync_mut/mcp/`). Rename to `simple_spipe_docgen`.
- Bootstrap script: `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` — must pass after Wave 3.
- `bin/simple` is the Rust seed (per `feedback_sspec_compile_pipeline.md`), so Cargo `mod` paths in `src/compiler_rust/.../mod.rs` need updating when files rename.

---

## 3. Scope Boundaries

**IN scope:**
- Rename source files, module paths, file extension `.sspec` → `.spipe`.
- Rename in-file strings/comments/identifiers (case-preserving: `sspec`→`spipe`, `SSpec`→`SPipe`, `SSPEC`→`SPIPE`).
- Update generator prefix `sspec_wrapped_entry_` → `spipe_wrapped_entry_` and regenerate fixtures.
- Merge skill+lib+lint-rules+guide into `doc/00_llm_process/spipe/`.
- Rename MCP tool `simple_sspec_docgen` → `simple_spipe_docgen`.
- Regenerate baremetal example artifacts from renamed source.

**OUT of scope:**
- Renaming dated `doc/09_report/.../sspec_*.md` filenames (historical record kept).
  - In-file narrative refs in those reports may be left as-is (they describe the *past* state when it was called sspec).
- Renaming inside vendored code (`src/compiler_rust/vendor/**`, `src/runtime/vendor/**`, `src/runtime/{miniaudio,stb_image,stb_truetype}.h`) per CLAUDE.md owned-code rule.
- Renaming inside `.claude/worktrees/` (parallel agent worktrees — they re-snapshot from main).

---

## 4. Wave Plan (serial — each wave is a separate commit)

> **Why serial, not parallel:** advisor flagged that the test-fixture wave (W2) depends on the generator change landing, and W3 (source rename) breaks bootstrap if any callsite is missed — must be the gating wave with bootstrap-from-scratch verification before W4. Parallel would either clobber files or push a half-rename that breaks `bin/simple`.

### Wave 1 — Skill + doc harness merge (LOW risk, no compile dep)

**Goal:** Land `doc/00_llm_process/spipe/` + `.claude/skills/spipe.md` + sstack/dev refs updated. Source code untouched.

**Steps:**
1. `mkdir -p doc/00_llm_process/spipe/`
2. Compose `doc/00_llm_process/spipe/INDEX.md` (one short index page; lists merged sub-docs and notes the rename).
3. Migrate content (consolidate, don't just concatenate):
   - `.claude/skills/sspec_loop.md` → `doc/00_llm_process/spipe/loop.md` (loop semantics)
   - `.claude/skills/lib/sspec.md` → `doc/00_llm_process/spipe/skill.md` (role + steps)
   - `doc/05_design/sspec_lint_rules_design.md` → `doc/00_llm_process/spipe/lint_rules.md`
   - `doc/06_spec/app/compiler/sspec_guide.md` → `doc/00_llm_process/spipe/guide.md`
4. Write `.claude/skills/spipe.md` thin entry-point (front-matter `name: spipe`, description, dispatch into `doc/00_llm_process/spipe/skill.md`).
5. Update `.claude/skills/sstack.md` 4 callsites: `/sspec` → `/spipe`. Also update Phase 4 row's "Cooperative Skill" column.
6. Search `.claude/agents/sstack/spec.md` and any agent definition referring to `/sspec`; update.
7. Update `tools/claude-plugin/sstack-lang/skills/sspec_loop.md` mirror — rename file to `spipe_loop.md` and update its content (this mirror gets republished as a Claude plugin).
8. Delete originals after the new files exist:
   - `.claude/skills/sspec_loop.md`
   - `.claude/skills/lib/sspec.md`
   - `doc/05_design/sspec_lint_rules_design.md` (or leave a 1-line redirect stub)
   - `doc/06_spec/app/compiler/sspec_guide.md` (or leave a 1-line redirect stub)
9. `git status` — should show ~10 changed/added files, no source-code changes.
10. Commit: `chore(skill): merge sspec → spipe under doc/00_llm_process/spipe/ (W1)`

**Verification:**
- `grep -rIn '/sspec\b' .claude/skills/ .claude/agents/` returns no hits.
- `.claude/skills/spipe.md` parses (front-matter valid).
- `doc/00_llm_process/spipe/INDEX.md` lists 4 merged docs.

**Exit gate:** Manual review of merged content fidelity (no information loss).

---

### Wave 2 — Test-fixture generator + regeneration (MEDIUM risk)

**Goal:** Change the wrapper-fixture generator prefix and regenerate fixtures so they emit as `.spipe_wrapped_entry_*.spl`.

**Steps:**
1. Read `src/compiler_rust/driver/src/cli/test_runner/execution.rs`. Locate the literal `"sspec_wrapped_entry_"` (or `format!("sspec_wrapped_entry_…")`).
2. Change to `"spipe_wrapped_entry_"`.
3. Delete all 35 existing `.sspec_wrapped_entry_*.spl` fixtures (and stale `.smf` builds) — they regenerate.
   - One-liner: `find test/ doc/ -type f -name '.sspec_wrapped_entry_*' -delete`
4. Also delete any `.simple/build/sspec_*` cached SMFs.
5. Run a single smoke test through `bin/simple test test/smoke/<some_smoke>_spec.spl` to force regeneration.
6. Verify a `.spipe_wrapped_entry_*` fixture appears.
7. `git status` — should show 1 generator file changed + ~35 deletions + ~35 fresh additions.
8. Commit: `chore(test-runner): generator emits spipe_wrapped_entry_ prefix (W2)`

**Verification:**
- `find test/ doc/ -name '.sspec_wrapped_entry_*' | wc -l` → `0`
- `find test/ doc/ -name '.spipe_wrapped_entry_*' | wc -l` → ≥ 1
- The smoke test still passes.

**Exit gate:** Smoke test passes with regenerated fixture.

---

### Wave 3 — Source rename + bootstrap verify (HIGH risk — gating)

**Goal:** Rename source files, update every `use`/`import`/`mod` callsite, and make the self-hosted bootstrap pass.

**Pre-flight:**
- Capture current bootstrap timing (sanity baseline).
- Snapshot file count: `git ls-files | wc -l` (per `feedback_destructive_upstream_detection.md`).

**Steps (in order — order matters):**
1. **Rust files first (Cargo `mod` graph):**
   - `git mv src/compiler_rust/compiler/src/lint/checker_sspec.rs checker_spipe.rs`
   - `git mv src/compiler_rust/driver/src/cli/migrate/sspec.rs spipe.rs`
   - Update `src/compiler_rust/compiler/src/lint/mod.rs` (or wherever `pub mod checker_sspec;` is declared) → `pub mod checker_spipe;` and any `use ::checker_sspec::*` → `checker_spipe`.
   - Update `src/compiler_rust/driver/src/cli/migrate/mod.rs`.
   - In-file: rename function/struct names containing `sspec` → `spipe` (case-preserving). Run `cargo check -p compiler_rust_compiler -p driver` to catch dangling refs.
2. **Simple stdlib files:**
   - `git mv src/lib/nogc_sync_mut/sspec.spl src/lib/nogc_sync_mut/spipe.spl`
   - `git mv src/lib/nogc_sync_mut/sspec.smf src/lib/nogc_sync_mut/spipe.smf` (if present — may regenerate)
   - `git mv src/compiler_rust/lib/std/src/spec/sspec_docgen.spl spipe_docgen.spl`
   - `git mv src/compiler_rust/lib/std/src/tooling/dashboard/collectors/sspec_collector.spl spipe_collector.spl`
   - Update every `use std.sspec`, `use nogc_sync_mut.sspec`, `import sspec_*` callsite. Use `grep -rln 'use std\.sspec\b\|use sspec\b\|nogc_sync_mut\.sspec\|nogc_sync_mut/sspec' src/ test/`.
3. **File extension `.sspec`:**
   - `git mv src/compiler/60.mir_opt/optimization_passes.sspec optimization_passes.spipe`
   - Find any reader of `.sspec` extension: `grep -rln '\.sspec\b\|"sspec"\|extension.*sspec' src/`. Update.
4. **Templates:**
   - `git mv .claude/templates/sspec_template.spl .claude/templates/spipe_template.spl`
   - Update any references in `.claude/skills/spipe.md` and agent definitions.
5. **Hand-written test specs:**
   - `git mv test/integration/app/sspec_quality_lint_spec.spl spipe_quality_lint_spec.spl`
   - `git mv test/unit/compiler/backend/sspec_system_test_spec.spl spipe_system_test_spec.spl`
6. **In-file strings (case-preserving) across renamed source files only** — leave content of historical reports alone:
   - `sspec` → `spipe`, `SSpec` → `SPipe`, `SSPEC` → `SPIPE` in `.spl`, `.rs`, `.toml` under `src/`, `test/`, `bin/`, `scripts/`.
7. **Run bootstrap-from-scratch (gating verification):**
   ```
   scripts/bootstrap/bootstrap-from-scratch.sh --deploy
   ```
   Per `feedback_extern_bootstrap_rebuild.md`, do NOT use `bin/simple build bootstrap` — it silently no-ops.
8. **Smoke run:**
   ```
   bin/simple test test/smoke/.spipe_wrapped_entry_compile_smoke_spec.spl
   ```
9. If bootstrap fails: do NOT push. Investigate, fix the missed callsite, re-run. Two retries max — then escalate to user.
10. `git ls-files | wc -l` — must equal pre-flight count (within rename delta). Drop = destructive upstream signal (see feedback memory).
11. Commit: `refactor(core): rename sspec → spipe across source + extension (W3)`

**Verification:**
- `bootstrap-from-scratch.sh --deploy` exits 0.
- `bin/simple` runs.
- `grep -rln 'sspec\|SSpec\|SSPEC' src/ test/ bin/ scripts/ --include='*.spl' --include='*.rs' --exclude-dir='vendor'` returns near-zero hits (only references inside the *generator* output and acceptable comments referring to the *old name historically*).

**Exit gate:** **Bootstrap green + smoke test green.** This is the load-bearing wave.

---

### Wave 4 — MCP + dashboards + examples regen + final INDEX (MEDIUM risk)

**Goal:** Catch the long tail — MCP tool name, dashboard tables, regenerated baremetal examples, doc index, narrative refs in non-historical docs.

**Steps:**
1. **MCP tool rename:**
   - Find dispatch table: `grep -rln 'simple_sspec_docgen' src/ tools/`
   - Rename the tool key/handler/registration to `simple_spipe_docgen`.
   - Update `.mcp.json` if it gets regenerated — verify after.
   - Restart MCP server (manual user step).
2. **Dashboard:**
   - `git mv doc/10_metrics/dashboard/tables/sspec_tests.sdn doc/10_metrics/dashboard/tables/spipe_tests.sdn`
   - Update the dashboard collector `spipe_collector.spl` (already renamed in W3) to write `spipe_tests.sdn`.
3. **Baremetal examples — regenerate, do NOT mv:**
   - Delete `examples/09_embedded/baremetal/baremetal/hello_riscv32_sspec.{elf,s}` and `riscv32_test/sspec_baremetal.h`.
   - Re-build the baremetal target so it regenerates `hello_riscv32_spipe.{elf,s}` and `spipe_baremetal.h` from the renamed source headers.
4. **Non-historical doc narrative refs** (selective sweep — exclude `doc/09_report/`):
   - `grep -rln 'sspec\|SSpec\|SSPEC' doc/ --exclude-dir='09_report' --include='*.md'`
   - Update the file paths/skill names in narrative; leave references to "the old sspec format" as historical context if they describe past state.
5. **Final INDEX:**
   - Update `doc/00_llm_process/spipe/INDEX.md` with the full migration manifest (what was renamed, what was kept).
   - Add 1-line entry to `doc/06_spec/INDEX.md` if it indexes `spipe_guide.md`.
6. **Verification scans:**
   - `find . -path './.claude/worktrees' -prune -o -path './build' -prune -o -path './target' -prune -o -path './.git' -prune -o -path './.jj' -prune -o -path './doc/09_report' -prune -o -type f -iname '*sspec*' -print` → empty.
   - MCP server tool list contains `simple_spipe_docgen`, not `simple_sspec_docgen`.
7. Commit: `chore(rename): MCP/dashboard/examples sspec → spipe; final INDEX (W4)`

**Exit gate:**
- Filename inventory clean (excluding `09_report/`, vendored, worktrees).
- MCP tool reachable under new name.
- `bin/simple test` golden-path smoke run still passes.

---

## 5. Resume Procedure (for restart later)

1. Read `.sstack/rename-sspec-to-spipe/state.md` — phase checklist + outputs.
2. Read this `PLAN.md` — full inventory + waves.
3. Run inventory drift check (some files may have moved since 2026-04-26):
   ```
   find . \( -path './.claude/worktrees' -o -path './build' -o -path './target' \
            -o -path './node_modules' -o -path './.git' -o -path './.jj' \) -prune \
        -o -type f -iname '*sspec*' -print | sort > /tmp/sspec_now.txt
   wc -l /tmp/sspec_now.txt   # baseline was 51 files on 2026-04-26
   ```
4. Identify the next un-checked wave in `state.md` → `## Phase Checklist` and the `## Wave Plan` section. Check the wave's `Verification` block to see whether it was already started.
5. **Critical pre-condition for ANY wave:** `git status` must be clean of unrelated changes. Stash or commit first.
6. **Wave order is mandatory:** W1 → W2 → W3 → W4. W3 must show a green bootstrap before W4 starts.
7. After completing each wave: tick its checkbox in `state.md`, write the output summary in `## Phase Outputs`, and create the wave's commit.

### Quick wave selector

| If state.md shows... | Resume at |
|---|---|
| `[ ] 1-dev` complete, no W1 commit | Wave 1 (skill+doc merge) |
| W1 commit exists, no `.spipe_wrapped_entry_*` fixtures | Wave 2 (generator) |
| W2 commit exists, `src/lib/nogc_sync_mut/sspec.spl` still exists | Wave 3 (source rename + bootstrap) |
| W3 commit exists, `simple_sspec_docgen` still in MCP tool list | Wave 4 (MCP+dashboards+examples) |
| All four wave commits exist + verification scans clean | Phase 6+ (refactor/verify/ship) |

### If something breaks mid-wave

- **Bootstrap fails after W3:** revert W3 commit (`jj abandon` the change), debug callsites, re-attempt. Do not push partial.
- **MCP tool unreachable after W4:** check `simple-mcp` dispatch table re-registered the renamed tool.
- **Wrapped-entry fixtures regenerate with the OLD prefix after W2:** the generator change in `execution.rs` didn't land — re-grep `sspec_wrapped_entry` in `src/compiler_rust/driver/`.

---

## 6. Risk Register

| Risk | Mitigation |
|---|---|
| Self-hosted bootstrap break (load-bearing) | W3 gating verification; revert wave on failure. |
| Hidden `.sspec` extension reader missed | grep `\.sspec\b` across `src/` before W3 commit. |
| MCP tool name break causes IDE/Claude failure | W4 verification = restart server, list tools. |
| Auto-regenerated fixtures revert filenames | W2 changes the generator FIRST, then deletes; never the reverse. |
| Historical reports lose discoverability | Keep filenames; only update forward-looking refs. |
| jj parallel agents clobber wave files | Pause parallel sstack tracks (per `feedback_submodule_race_parallel_dev.md`) before W3. |
| Destructive upstream rebase strips waves | Run `git ls-files \| wc -l` pre/post each wave; abort on drop (per `feedback_destructive_upstream_detection.md`). |

---

## 7. Open Questions (blocking)

None blocking — user gave green light "merge them make spipe. rename too" on 2026-04-26. Default name expansion: **SPipe = Simple Pipe (spec→test→report pipeline)**. If user later prefers a different expansion, only `INDEX.md` and `.claude/skills/spipe.md` description need a touch-up.

---

## 8. Cross-Reference

- State file: `.sstack/rename-sspec-to-spipe/state.md`
- SStack skill: `.claude/skills/sstack.md`
- Memory entries that constrain this work:
  - `feedback_extern_bootstrap_rebuild.md` — use `bootstrap-from-scratch.sh --deploy`, not `bin/simple build bootstrap`
  - `feedback_sspec_compile_pipeline.md` — `bin/simple` is the Rust seed; SMF cache is broken
  - `feedback_destructive_upstream_detection.md` — file-count guard before/after each wave
  - `feedback_submodule_race_parallel_dev.md` — pause parallel /dev tracks before W3
  - `feedback_write_tool_silent_drops.md` — verify W3 with `grep`+`jj log`, not Read
