# SAML plan v2 — LSP-checked evidence, BAML-executed runtime (2026-08-10)

## Status — 2026-08-10 (post-implementation)

| Lane | Owner | Status |
|---|---|---|
| L1 — spec-coverage core (`spec_coverage.spl`) | A1 | LANDED — `discover_spec_coverage`, 11/11 spec, lint 0 errors |
| L2 — surfaces (analysis merge, CLI `--specs`, MCP `spec_dir`, IDE `ide_saml_evidence`) | A2/A3/A4 | LANDED — `analyze_module_with_specs`/`analyze_function_with_external` in `analysis.spl`; `--specs DIR` on `analyze`/`check`; `spec_dir` on MCP `saml_analyze` verified over real stdio JSON-RPC; `ide_saml_evidence` wired, self-probe `checks=5/5` |
| L3 — LSP checks the analysis (`E-SAML-1810`) | A2 | LANDED — external-only evidence with no counter-example warns, external coverage lifts `unevidenced`→`tested`, never →`red_proven` |
| L4 — BAML CLI hygiene + docs | A5 (this wave) | `baml-cli` check: **skipped — not installed on `PATH` in this environment, no new dependency added.** Docs updated (`saml_guide.md` "Executing via BAML" section, `saml_ide_integration.md`, feature-expert skill, `.claude/commands/dev.md` §5). |

Verification the orchestrator re-ran itself (not just relayed): 45/45 unit
spec green (40 original + 5 new external-coverage cases), all touched files
lint 0 errors, IDE self-probe `checks=5/5`, MCP `saml_analyze` round-trip
over real stdio JSON-RPC showing an `external:` entry in the report. Runtime
LLM execution (D1) and `.vsix` packaging (D2) remain permanently out of
scope, not deferred.

Supersedes the execution lanes (S14–S23) of
`saml_parallel_agents_plan_2026-08-09.md`. Everything already landed
(parser/analysis/emit, CLI, MCP `saml_analyze`, Simple IDE, 40-test spec)
stays as-is.

## Decisions

- **D1 — BAML is the runtime.** SAML never calls an LLM itself. `emit_baml`
  is the execution boundary; BAML's own runtime does transport, retries,
  schema-aligned parsing, tracing. Lanes S14–S23 / S24–S30 / S19 of the old
  plan are **dropped**, not deferred. If a native runtime is ever wanted,
  that is a new plan.
- **D2 — VS Code = MCP tool + rendering guide, no `.vsix`.** Declared
  sufficient by the user. Simple IDE remains the implemented editor surface.
- **D3 — evidence must include *external* sspec unit tests.** Today
  `covering_tests` (`analysis.spl:215-220`) sees only `test` blocks inside
  the `.saml` file. A real spec in `test/**/*_spec.spl` exercising an
  `llm fn` is invisible → functions read `unevidenced` despite coverage.
  Closing this is the whole point of v2.

## Lanes

### L1 — sspec coverage discovery (core, blocks L2/L3)
New `src/lib/common/saml/spec_coverage.spl`:

- `discover_spec_coverage(fn_names: [text], spec_sources: [(path, text)]) -> [(fn, "external:<path>:<it-title>")]`
  Pure function over pre-read sources — no fs access in `common/` (tier
  rule); callers read files. Match rule: inside an `it "…":` block, a
  call-site token `FnName(` (word-boundary; skip comments/strings) binds
  that it-title to FnName.
- Merge into `analyze_function`: `covering.push(...)` after the `.saml`-local
  loop; `evidence_state` unchanged (count includes external).
- Report: `evidence:` line already prints `tests=[...]`; external entries
  carry the `external:` prefix so clients can distinguish.
- **Falsifiability fixture**: one spec source that names the fn in a comment
  only, one wrong-arity — both must NOT bind. Sabotage probe per /dev.

### L2 — wire discovery into the three surfaces
- CLI (`src/app/saml/main.spl`): `analyze`/`check` gain `--specs <dir>`
  (default `test/`), glob `*_spec.spl`, feed L1.
- MCP (`simple_lsp_mcp/tools.spl`): `saml_analyze` gains optional
  `spec_dir` argument, same default.
- Simple IDE (`src/app/ide/saml_analysis.spl`): `ide_saml_diagnostics` et
  al. accept optional pre-read spec sources; feature-report probe updated.
One renderer (`emit_analysis_report`) → no per-surface formatting work.

### L3 — LSP *checks* the analysis (the "lsp can check unit tests" clause)
- New warning `E-SAML-1810: function <f> is tested only by external specs;
  add a # counter-example` — external coverage lifts to `tested`, never to
  `red_proven` (counter-examples stay in-file, keeping the falsifiability
  contract local and reviewable).
- `check` exit-code contract unchanged; new warning is warning-severity.
- Guide + dev.md §5 updated: evidence line now names external specs;
  "unevidenced despite a spec" is a fixed bug, note the `--specs` knob.

### L4 — BAML bridge hygiene (small)
- `generate --target baml` output validated once against a real BAML CLI if
  present on PATH; if absent, skip with a printed notice (no new dep).
- Doc: `doc/07_guide/infra/llm/saml_guide.md` gains "Executing via BAML"
  section: generate → `baml-cli` → call from Simple via SFFI/process, with
  the explicit statement that SAML itself never executes prompts.

## Parallel-agent execution plan

Runtime LLM is DROPPED (user-confirmed 2026-08-10) — no agent works on it.
Shared working copy: each agent touches ONLY its owned files below; no two
agents share a file. Orchestrator (main session) verifies every agent's
claim by re-running its verdict lines itself before integration.

### Wave 1 — foundation (one agent, blocking)

**A1 `spec-coverage-core`** — owns:
- NEW `src/lib/common/saml/spec_coverage.spl`
- NEW `test/01_unit/lib/saml/spec_coverage_spec.spl`
- NEW `test/01_unit/lib/saml/fixtures/covering_spec_source.spl` (fixture
  text, not a runnable spec — keep out of the runner glob by placing under
  `fixtures/`)

Contract (frozen now so Wave 2 can code against it in parallel):
```
# spec_coverage.spl exports exactly:
fn discover_spec_coverage(fn_names: [text], spec_paths: [text], spec_sources: [text]) -> [text]
#   returns entries "fn_name\texternal:<path>:<it_title>"
#   (tab-separated; caller splits — avoids a struct export dependency)
fn spec_files_under(root: text) -> [text]   # NOT here — see A2; common/ is pure
```
Match rule: a binding exists iff, inside an `it "…":` block body, a token
`FnName(` appears at a word boundary outside `#` comments and string
literals. MUST-NOT-bind fixtures: name in a comment, name in a string,
name as a substring (`MyExtract(` for `Extract`), call outside any `it`.
DoD: spec 10+ cases, sabotage probe (break the word-boundary check →
substring fixture goes RED), lint 0 errors.

### Wave 2 — surfaces (three agents, parallel, start after A1's contract
lands — they depend on the export signature only, so they may start
immediately and integration-test after A1 finishes)

**A2 `analysis-merge-and-cli`** — owns:
- `src/lib/common/saml/analysis.spl` (merge external entries into
  `covering_tests` before `evidence_state` at line ~251; external coverage
  counts toward `tested`, NEVER lifts to `red_proven`; add warning
  `E-SAML-1810` when a fn's only evidence is external and it has no
  counter-example)
- `src/app/saml/main.spl` (`--specs <dir>` on `analyze`/`check`, default
  `test/`; the fs walk lives HERE, in app tier, feeding pure A1 fn)
- `test/01_unit/lib/saml/saml_spec.spl` (extend; keep existing 40 green)
DoD: 40 old + new cases green; probe: point `--specs` at a dir containing
the covering fixture → fn lifts unevidenced→tested; empty dir → unchanged.

**A3 `mcp-surface`** — owns:
- `src/app/simple_lsp_mcp/tools.spl` + `main.spl` (optional `spec_dir`
  argument on `saml_analyze`, default `test/`, forwarded as `--specs`)
DoD: real stdio JSON-RPC round-trip showing an `external:` entry in the
report; missing-dir arg falls back to default, never errors.

**A4 `ide-surface`** — owns:
- `src/app/ide/saml_analysis.spl` (new `ide_saml_evidence(source, path,
  spec_paths, spec_sources)`; existing four functions unchanged so
  `ide_office_plugin_suite_spec` stays 21/21 without edit — if the
  feature-report line must change, A4 owns that spec edit too)
DoD: self-probe extended to `checks=5/5`; IDE suite green.

### Wave 3 — docs & closure (one agent + orchestrator)

**A5 `docs-and-baml`** — owns:
- `doc/07_guide/infra/llm/saml_guide.md` ("Executing via BAML" section +
  external-evidence semantics), `saml_ide_integration.md` (evidence line
  now carries `external:` entries; `--specs`/`spec_dir` knobs)
- `doc/00_llm_process/feature_expert/saml/skill.md` refresh
- `.claude/commands/dev.md` §5: note external specs lift to `tested` only
- L4 check: run `emit_baml` output through `baml-cli` IF on PATH, else
  print skip notice; record result in guide. No new dependency.

**Orchestrator (not delegated):** re-run every verdict line personally
(40+ spec, IDE 21/21, MCP round-trip, one sabotage probe per agent),
cross-agent integration run (`analyze --specs test/` on the resume
fixture), lint all touched files to 0 errors, then the /dev Final Step
Check. Any agent claim not reproducible by the orchestrator is rejected,
not relayed.

### Known traps to hand each agent
- `bin/simple` symlink may be missing — use
  `bin/release/x86_64-unknown-linux-gnu/simple` directly.
- 60s CPU guard SIGTERMs long runs — detach lint with `setsid nohup`.
- `examples`/`and_then` are broken in named-argument position.
- `{{ … }}` in Simple text literals interpolates — fixtures go on disk.
- `simple test <absolute path>` runs nothing and exits 0 — relative paths.
- Worktree-isolated agents have no built binary — agents run in the shared
  WC, which is WHY file ownership above is exclusive.

## Out of scope (permanently, per D1/D2 — user-confirmed drop)
Native LLM transport, retries, schema-aligned reply parsing, tracing spans,
evidence sidecars from live runs, reference apps, `.vsix` packaging.
