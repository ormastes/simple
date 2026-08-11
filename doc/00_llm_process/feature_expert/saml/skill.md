# Feature Expert — SAML (`simple-saml`)

## Role

Own process knowledge for **SAML — "Simply A Made-up Language"**, a declarative
language for typed LLM functions. External name: `simple-saml`.

> **Never confuse this with OASIS SAML** (XML SSO / federated identity). No
> security semantics exist here. Say `simple-saml` in external text.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Feature Links

- Research: `doc/01_research/infra/llm/saml_research_2026-08-09.md`
- Plan v1 (45 parallel lanes; execution lanes S14-S23 DROPPED): `doc/03_plan/infra/llm/saml_parallel_agents_plan_2026-08-09.md`
- Plan v2 (current — LSP-checked evidence, BAML-executed runtime): `doc/03_plan/infra/llm/saml_lsp_evidence_plan_2026-08-10.md`
- Design (authoritative): `doc/05_design/infra/llm/saml_baml_integration_research_design_plan_2026-08-09.md`
- Guide (what actually exists): `doc/07_guide/infra/llm/saml_guide.md`
- IDE integration: `doc/07_guide/infra/llm/saml_ide_integration.md` (owned by a separate lane)
- Source: `src/lib/common/saml/`

## Source Entry Points

| File | Role |
|---|---|
| `src/lib/common/saml/ir.spl` | Canonical records (`SamlModule`, `SamlClass`, `SamlFunction`, …) + type/attribute helpers. Start here. |
| `src/lib/common/saml/parser.spl` | `parse_saml(source, path) -> SamlModule`. Line-oriented, indentation-aware, tolerant (bad line → diagnostic, not abort). |
| `src/lib/common/saml/analysis.spl` | `analyze_module`/`analyze_function` (in-file evidence only, unchanged) plus `analyze_module_with_specs`/`analyze_function_with_external` (landed 2026-08-10 — fold in `discover_spec_coverage` results; external evidence lifts `unevidenced`→`tested`, never →`red_proven`; emits `E-SAML-1810` when external is the only evidence and there's no counter-example). Purely static. |
| `src/lib/common/saml/spec_coverage.spl` | NEW 2026-08-10. `discover_spec_coverage(fn_names, spec_paths, spec_sources) -> [text]` — pure match over pre-read sspec sources, `"fn_name\texternal:<path>:<it_title>"` entries. Match rule: `FnName(` at a word boundary inside an `it "…":` body, outside comments/strings. |
| `src/lib/common/saml/emit.spl` | Projections: BAML, projection-loss list, SDN manifest, analysis report, Markdown manual. Unchanged by this wave. |

## Surfaces consuming spec_coverage (landed 2026-08-10)

- CLI `src/app/saml/main.spl`: `analyze`/`check` gain `--specs DIR` (default
  `test/`); the filesystem walk (`discover_spec_files`) lives here, in app
  tier — `common/` stays pure.
- MCP `src/app/simple_lsp_mcp/tools.spl`/`main.spl`: `saml_analyze` gains
  optional `spec_dir`, forwarded as `--specs <spec_dir>`; empty/omitted
  falls back to the CLI default.
- Simple IDE `src/app/ide/saml_analysis.spl`: new
  `ide_saml_evidence(source, path, spec_paths, spec_sources)`; the other
  four IDE functions are untouched. IDE self-probe: `checks=5/5` (was
  `4/4`).
- Spec: `test/01_unit/lib/saml/saml_spec.spl` extended to 45/45 green (40
  original + 5 external-coverage cases); `test/01_unit/lib/saml/spec_coverage_spec.spl`
  is the dedicated 11/11 spec for the new module.
- Runtime LLM execution is **permanently dropped**, not deferred — see
  `doc/03_plan/infra/llm/saml_lsp_evidence_plan_2026-08-10.md` D1. Execution
  is BAML's job (`generate --target baml` → `baml-cli` → SFFI/process call
  from Simple); SAML itself never opens a connection or calls a model.
  `baml-cli` was not present on `PATH` when this was last checked
  (2026-08-10) — the integration is documented, not locally exercised.
- VS Code `.vsix`: explicitly out of scope per user decision D2 — MCP tool
  + rendering guide (`saml_ide_integration.md`) is the declared-sufficient
  surface.

Design invariant: the `.saml` file is authoritative; every other artifact is a
projection of `SamlModule`. No emitter reparses another emitter's output, and
declaration order is semantic — never sort.

## Traps a future agent WILL hit

1. **`examples` is a keyword.** `struct X: examples: text` declares and reads
   fine, but `X(examples: v)` is a parse error: `function arguments: expected
   Comma, found Colon`. Root cause: `"examples" => TokenKind::Examples` at
   `src/compiler_rust/parser/src/lexer/identifiers.rs:290` (Gherkin data-table
   token). The SAML field is therefore named **`example_cases`**, not
   `examples` — do not "fix" that rename. Bug:
   `doc/08_tracking/bug/examples_identifier_rejected_in_named_argument_position_2026-08-10.md`.
   Note the parse failure **exits 0**.
2. **`{...}` in a text literal is interpolation.** Any braces inside a Simple
   `"..."` literal are parsed as an interpolation, so SAML prompt syntax
   (`{{ var }}`, `{{ saml.output_format }}`) written directly in `.spl` source
   must be built by concatenation or escaped. This is why the parser matches
   `"{{"` / `"}}"` by `index_of` on runtime strings rather than by literal
   templates.
3. **`bin/simple` is the Rust bootstrap seed** (29,577,536 bytes, mtime
   2026-08-09 04:50) and prints a warning saying so. Any language behavior you
   measure is the seed's, not the pure-Simple self-hosted compiler's. Record
   binary identity with every measurement.
4. **The spec exists and is non-vacuous.** `test/01_unit/lib/saml/saml_spec.spl`
   runs 45/45 green (exit 0; 40 original + 5 external-coverage cases added
   2026-08-10); sabotaging `evidence_state` takes it down. Re-run it after
   any change to the modules — it is the fastest signal.
5. **CLI works, but not as `bin/simple saml`.** `src/app/saml/main.spl` is
   registered in `src/app/cli/dispatch/table.spl`, yet `bin/simple saml ...`
   fails with `file not found: saml` because the Rust seed's argv parser never
   consults that table (control: the long-registered `targets` fails the same
   way). Use `bin/simple run src/app/saml/main.spl <subcommand> <file>`.
   Never claim a capability works that is not reachable through the binary
   users run — state the blocker.
6. **Comment cases are validated.** A `# example:` counts only if it names this
   function, has matching arity (commas inside string literals do not split
   arguments), and states an expectation after `=>`; otherwise it is dropped
   and reported as `E-SAML-1800: ignored comment case — <fix>`. What is still
   NOT checked: that the expectation's field exists on the schema, and that the
   case ever executed. `red_proven` means "well-formed counter-example written",
   not "observed to fail" — wiring execution is the top open item.

## Affected Layers

- `src/lib/common/` (pure functions tier — no I/O in these four files; callers
  do the file reads).
- Future: `src/app/` (CLI), LSP/IDE surface consuming `emit_analysis_report`.

## Known Blockers / Next Work

- Done: spec landed (45/45), CLI/MCP/IDE all wired, all three consume the
  single `emit_analysis_report` renderer.
- Still open: `bin/simple saml ...` does not work as a direct subcommand —
  the Rust seed's argv parser never consults the dispatch table; use
  `bin/simple run src/app/saml/main.spl <sub> <file>` until the pure-Simple
  binary is rebuilt and deployed.
- Still open: `red_proven` means "well-formed counter-example written", not
  "observed to fail" — no execution wiring exists or is planned (D1, native
  runtime lanes dropped permanently).
- Still open: `baml-cli` round-trip has never been exercised in this repo's
  environment (not installed on `PATH` as of 2026-08-10); re-verify on a
  machine that has it before treating the BAML hand-off as proven end to
  end.
- Revert `example_cases` → `examples` only after the keyword bug is fixed.

## Verification Commands

```bash
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"   # always record identity
bin/simple test test/01_unit/lib/saml/saml_spec.spl                     # once the spec exists
sh scripts/check/lint-cached.shs src/lib/common/saml/<file>.spl         # one file at a time
```

Require a `SPEC FILE VERDICT ... executed=N` line — exit 0 alone proves nothing
here, and `simple test` with an absolute path runs nothing and still exits 0.

## Update Rule

When any SAML research, design, plan, spec, implementation, or verification
artifact changes, update this file with the new links and current handoff notes
in the same commit as the work (`.claude/rules/vcs.md`).
