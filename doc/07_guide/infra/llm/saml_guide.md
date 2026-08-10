# SAML Guide — what exists today

**Scope note:** this guide describes only what is implemented in
`src/lib/common/saml/{ir,parser,analysis,emit,spec_coverage}.spl` plus the
CLI/MCP/IDE surfaces that consume them. Anything in the design doc but not
implemented is marked as such. Where a capability is not reachable from the
binary users run, the blocker is stated instead of the capability.

## 1. What SAML is — and the name collision

SAML here is **"Simply A Made-up Language"**, published externally as
**`simple-saml`**. It is a small declarative language for typed LLM functions:
you declare the schema the model must return, the prompt, the client policy,
and the evidence that backs the function.

> **It is NOT OASIS SAML**, the XML single-sign-on / federated-identity
> standard. There is no security, assertion, or SSO semantics here at all. Use
> the `simple-saml` spelling in any external-facing text, and never abbreviate
> to "SAML" in a security context.

A `.saml` file is authoritative. Everything else — BAML source, an SDN
manifest, a Markdown manual, an analysis report — is a *projection* of the
parsed `SamlModule` (`ir.spl`).

## 2. Syntax the parser actually accepts

`parse_saml(source, source_path) -> SamlModule` (`parser.spl:165`) is
line-oriented and indentation-aware, and **tolerant**: an unrecognised line
becomes a `SamlDiagnostic` rather than aborting the file, so an editor always
has a partial model. Top-level declarations must start at column 0; their
bodies are indented.

```saml
module resume

class Resume:
    name: text @alias("candidate_name") @description("Full legal name")
    email: text? @sensitive(pii)
    skills: [text]

enum Seniority:
    junior
    staff @alias("senior_staff")

struct RunStats:
    tokens: i64

# example: ExtractResume("Grace Hopper, Rear Admiral") => name == "Grace Hopper"
# counter-example: ExtractResume("") => error
@trace
@parse(strictness: strict)
llm fn ExtractResume(raw: text) -> Resume:
    client: fast
    prompt:
        """
        Extract the resume from:
        {{ raw }}
        {{ saml.output_format }}
        """

test resume_extraction:
    functions:
        - ExtractResume
    assert:
        - name is not empty
    evidence:
        source: fixture
```

What each construct means to the parser:

| Construct | Parsed into | Notes |
|---|---|---|
| `module NAME` | `SamlModule.name` | one per file |
| `class NAME:` | `SamlClass` | LLM-visible schema; projects to a BAML `class` |
| `enum NAME:` | `SamlEnum` | one member per line, `@alias("...")` optional |
| `struct NAME:` | `SamlStruct` | **native-only**; never projected into the BAML schema, and using one as an `llm fn` return type is warning `E-SAML-1600` |
| `llm fn NAME(params) -> Ret:` | `SamlFunction` | body accepts `client:` and `prompt:` + a `"""` block |
| `test NAME:` | `SamlTest` | sub-blocks `functions:`, `assert:` (`- item` lists) and `evidence:` → `source:` |

Types: `Name: [Type]?` — the parser strips a trailing `?` (optional) and
surrounding `[]` (list) and stores the bare element name plus two flags
(`_parse_typed_name`, `parser.spl:72`). Legal `source:` values recognised by
the analysis ladder are free text; the design doc names `fixture`, `replay`,
`simulated_provider`, `live_provider`.

**Attributes.** A trailing run of `@attr` / `@attr(...)` is split off any
declaration line by `split_attributes` (`parser.spl:44`), which tracks paren
depth so `@parse(strictness: strict)` survives. Attributes are stored as **raw
source text**, so unknown attributes round-trip instead of being dropped.
Recognised today:

- Field level: `@alias("wire_name")`, `@description("...")`, `@sensitive(pii)`
- Enum member: `@alias("...")`
- Function level: any attribute; `@trace`, `@parse(strictness: X)` and
  `@redact` are the ones the analysis reads (`has_attribute` /
  `attribute_body`, `ir.spl:184`).

**Prompts.** A `"""` block is captured verbatim, one trimmed line per source
line. `{{ name }}` interpolations are extracted by `prompt_variables`
(`analysis.spl:49`); a `{{ Head(...) }}` call form keeps only the head name.
`{{ saml.output_format }}` is the special marker that renders the expected
schema to the model.

## 3. `# example:` and `# counter-example:` — and why the negative half matters

Comment-embedded tests sit immediately above a declaration and are attached to
the next `llm fn`:

```
# example: ExtractResume("Grace Hopper, Rear Admiral") => name == "Grace Hopper"
# counter-example: ExtractResume("") => error
```

`parse_example_comment` (`parser.spl:141`) splits on `=>` into
`input_text` / `expect_text`; a case with no `=>` keeps the whole body as
input. `kind` is `"example"` or `"counter_example"`.

**Why counter-examples are mandatory in practice:** an oracle that has never
failed proves nothing. A suite of positive examples is satisfied by an
implementation that returns a constant, and by an assertion that is a
tautology. A `# counter-example:` is the deliberate-red half — the input that
*must* be rejected. Until an oracle has demonstrated it can fail, its green is
not evidence. This is exactly why the ladder in §4 puts `red_proven` above
`tested`, and why `analyze_function` emits
`E-SAML-1800: no # counter-example: — the oracle has never been shown to fail`
against a function that is tested but has no negative case.

> **Field-name trap:** the IR field holding these is
> `SamlFunction.example_cases`, **not** `examples`. `examples` is a keyword in
> the seed parser and cannot be used as a named constructor argument — see
> `doc/08_tracking/bug/examples_identifier_rejected_in_named_argument_position_2026-08-10.md`.

## 4. What the analysis reports

`analyze_module(module) -> SamlAnalysis` (`analysis.spl:237`) produces one
`SamlFunctionAnalysis` per `llm fn` plus module-level rollups. It is
**deliberately static** — it never claims a function produces correct output,
only what is declared, what is bound, and what evidence exists.

**Evidence ladder** (`evidence_state`, `analysis.spl:126`):

| State | Condition |
|---|---|
| `unevidenced` | no declared test, no `# example:` |
| `examples_only` | comment examples but no `test` block binds the function |
| `tested` | at least one `test` block lists it under `functions:` |
| `red_proven` | at least one `# counter-example:` **and** some positive evidence |

Warnings emitted (codes match the design doc's `E-SAML-1xxx` family):

| Code | Fires when |
|---|---|
| `E-SAML-1100` | class unreachable from any `llm fn` (orphan schema, module-level) |
| `E-SAML-1200` | return type is neither a primitive nor a declared class/enum |
| `E-SAML-1300` | prompt references an unbound `{{ var }}`; or prompt never renders `{{ saml.output_format }}` |
| `E-SAML-1500` | no `client:` policy declared |
| `E-SAML-1600` | a native-only `struct` used as an LLM-visible return type |
| `E-SAML-1800` | evidence gaps: unevidenced / examples-only / tested-but-no-counter-example |
| `E-SAML-1810` | a function's only evidence is external specs (`--specs`/`spec_dir`) and it has no in-file `# counter-example:` |
| `E-SAML-1900` | reaches a `@sensitive(...)` field but declares no `@redact` policy |

### External sspec coverage (`--specs` / `spec_dir`, landed 2026-08-10)

`analyze`/`check` (CLI) and the `saml_analyze` MCP tool now also look for
coverage in `test/**/*_spec.spl` files, not just `test:` blocks and
`# example:` comments inside the `.saml` file itself:

- CLI: `analyze <file.saml> [--specs DIR]` / `check <file.saml> [--specs DIR]`
  — `--specs` defaults to `test/`, walked for `*_spec.spl` files
  (`src/app/saml/main.spl:discover_spec_files`).
- MCP: `saml_analyze` gains an optional `spec_dir` argument, forwarded as
  `--specs <spec_dir>`; omitted or empty falls back to the CLI default
  (`src/app/simple_lsp_mcp/tools.spl:run_saml_analyze`).
- Match rule (pure, `src/lib/common/saml/spec_coverage.spl:discover_spec_coverage`):
  inside an `it "…":` block body, a call-site token `FnName(` at a word
  boundary, outside comments and string literals, binds that spec's
  `it`-title to `FnName`. A name only inside a comment, inside a string, or
  as a substring of a longer identifier does **not** bind.
- Effect on the evidence ladder (`analysis.spl:analyze_module_with_specs`):
  external coverage lifts a function from `unevidenced` to `tested`. It
  **never** lifts a function to `red_proven` — that rung still requires an
  in-file `# counter-example:`, keeping the falsifiability contract local
  and reviewable. If a function's *only* evidence is external and it has no
  counter-example, `E-SAML-1810` fires as a reminder.
- The `evidence:` line's `tests=[...]` list marks external hits with an
  `external:<path>:<it_title>` prefix so a reader (or an editor client) can
  tell in-file `test:` blocks apart from sspec-discovered coverage, e.g.:

  ```
  evidence: tested tests=[external:test/.../greet_spec.spl:greets someone by name] examples=0 counter=0
  ! E-SAML-1810: function Greet is tested only by external specs; add a `# counter-example:` to reach red_proven
  ```

- `analyze_module`/`analyze_function` (no specs) are unchanged and still
  usable directly; `analyze_module_with_specs`/
  `analyze_function_with_external` are the specs-aware variants layered on
  top — source-compatible, nothing existing broke.

Binding rules worth knowing: a `{{ var }}` counts as bound if it names a
parameter, starts with `saml.`, or has a capitalised head (treated as a
template call resolved elsewhere). `reachable_types` (`analysis.spl:78`) walks
class fields transitively, so a function's *real* schema surface — not just its
return type — is what gets checked for sensitive fields and orphans.

## 5. The four projections

All in `emit.spl`; all read the same `SamlModule` (reports also take the
`SamlAnalysis`). No emitter reparses another's output, and none reorders
declarations — field, enum, and union order are semantic.

| Function | Output |
|---|---|
| `emit_baml(module)` | BAML-compatibility source. `baml_prompt_body` rewrites SAML prompt context names onto BAML equivalents. |
| `baml_projection_losses(module)` | The list of SAML semantics with no BAML spelling. This is what makes "BAML-compatible" an honest claim rather than a silent truncation — read it, don't skip it. |
| `emit_sdn_manifest(module, analysis)` | SDN manifest of the module plus its analysis rollup. |
| `emit_analysis_report(analysis)` | The compact report: one block per function, warnings inline. **One renderer** shared by LSP hover, the IDE panel, and agent tooling, so the human view and the machine view cannot drift. |
| `emit_markdown_manual(module, analysis)` | Human-facing Markdown manual, with an evidence badge per function. |

(That is five entry points across four projection targets: BAML, SDN, report,
manual — `baml_projection_losses` is the honesty companion to `emit_baml`.)

## 6. How to use it today

Three surfaces work as of 2026-08-10. One does not.

### CLI — works, but not as `bin/simple saml`

`src/app/saml/main.spl` implements `check`, `analyze`,
`generate --target baml|markdown|sdn [--out]`, and `doc`, and it is registered
in `src/app/cli/dispatch/table.spl`. Run it directly:

```bash
bin/simple run src/app/saml/main.spl analyze path/to/module.saml
bin/simple run src/app/saml/main.spl check path/to/module.saml     # rc=1 on errors
bin/simple run src/app/saml/main.spl generate --target baml path/to/module.saml
```

**`bin/simple saml ...` does NOT work** — it fails with `file not found: saml`.
`bin/simple` is the Rust seed and its argv parser never consults the Simple
dispatch table, so the registration only becomes live once the pure-Simple
binary is rebuilt. This is a property of the seed, not of the SAML entry: the
long-registered `targets` command fails the same way.

### MCP / editor — works today

The LSP MCP server exposes a `saml_analyze` tool taking `{"file": "..."}` and
returning the analysis report as text. Verified over real stdio JSON-RPC: the
server lists all eleven pre-existing `lsp_*` tools plus `saml_analyze`, and a
`tools/call` returns the full report. No rebuild is needed because `.mcp.json`
launches the server in source mode. See
`doc/07_guide/infra/llm/saml_ide_integration.md`.

### Simple IDE — works today

`src/app/ide/saml_analysis.spl` provides `ide_saml_diagnostics` (line-anchored
`line:severity:message` for inline squiggles), `ide_saml_hover` (per-function
card), `ide_saml_panel` (module view), and `ide_saml_manual`, plus (landed
2026-08-10) `ide_saml_evidence(source, path, spec_paths, spec_sources)`, which
wires `analyze_module_with_specs` straight into the shared
`emit_analysis_report` renderer so the IDE sees external-spec coverage too. It
is registered as a row in `ide_feature_check_report`; its self-probe reports
`checks=5/5` (was `4/4` before the fifth function landed).

### Library

SAML is also reachable directly as library calls from Simple code:

```simple
use std.common.saml.parser.{parse_saml}
use std.common.saml.analysis.{analyze_module}
use std.common.saml.emit.{emit_analysis_report, emit_baml, emit_markdown_manual}

fn main():
    val src = read_file("resume.saml")
    val module = parse_saml(src, "resume.saml")
    val analysis = analyze_module(module)
    print(emit_analysis_report(analysis))
```

Other honest limits:

- **Spec suite landed and is non-vacuous.** `test/01_unit/lib/saml/saml_spec.spl`
  runs 45 tests (40 original + 5 external-coverage cases added 2026-08-10):
  `SPEC FILE VERDICT ... declared>=45 executed=45 passed=45 failed=0`, exit
  0. Sabotaging `evidence_state` to always return `"tested"` drops the
  passing count and reverting restores 45/45, so the suite can actually
  fail. `test/01_unit/lib/saml/spec_coverage_spec.spl` is the dedicated
  11/11 spec for `discover_spec_coverage` itself.
- **Comment cases are validated, not merely counted.** A `# example:` only
  counts toward the evidence ladder if it names *this* function, passes the
  right number of top-level arguments (commas inside string literals do not
  split arguments), and states an expectation after `=>`. A case failing any of
  those is dropped from the count and reported as
  `E-SAML-1800: ignored comment case — <what to fix>`. Verified against a
  fixture with a wrong callee, a wrong arity, and a missing expectation: all
  three were rejected with a message naming the fix, and the function stayed at
  `unevidenced`. This closes the obvious self-certification hole — an author
  cannot raise a rung just by typing a comment.
- **Still not checked:** that the expectation's field exists on the reachable
  schema, and that the case was ever *executed*. `red_proven` therefore means
  "a well-formed counter-example is written", not "observed to fail". Wiring
  execution is the top open item.
- **Older note, now superseded:** the LSP and IDE surfaces described in §6 did
  not exist when this guide was first drafted. They do now. IDE
  integration is tracked separately in
  `doc/07_guide/infra/llm/saml_ide_integration.md`.
- **No runtime.** Nothing here calls a model. There is no execution, no
  provider, no receipts. The analysis is fully static by design; runtime facts
  (latency, tokens, repairs, evaluator verdicts) are a separate concern (design
  doc §14.9).
- **`bin/simple` is the Rust seed** (29,577,536 bytes, mtime 2026-08-09
  04:50); it prints a warning saying so on every run. Language-level behavior
  you observe is the seed's, not the pure-Simple self-hosted compiler's.

## 7. Executing via BAML

**SAML never calls a model.** This is a permanent decision (D1 in
`doc/03_plan/infra/llm/saml_lsp_evidence_plan_2026-08-10.md`), not a
staging step — the native-runtime lanes (S14–S23 of the original
2026-08-09 plan: transport, retries, schema-aligned reply parsing, tracing
spans, evidence sidecars from live runs) are **dropped**, not deferred. If
native execution is ever wanted, that requires a new plan and a new
decision, not a resumption of the old one.

The execution boundary is BAML itself:

1. Project the `.saml` module to BAML source:
   ```bash
   bin/simple run src/app/saml/main.spl generate --target baml path/to/module.saml --out module.baml
   ```
   Read `baml_projection_losses(module)`'s output first — it lists any SAML
   semantics (e.g. native-only `struct` return types) with no BAML spelling,
   so "BAML-compatible" is never a silently-truncated claim.
2. Hand `module.baml` to the BAML toolchain (`baml-cli generate`, or
   whatever the installed BAML version calls it) to produce its client code
   and runtime bindings. That is entirely outside this repo's SAML modules.
3. Call the generated BAML client from Simple via SFFI or a subprocess —
   the same pattern as any other external-runtime integration in this repo.
   BAML's own runtime does the transport, retries, schema-aligned parsing,
   and tracing; SAML's job stops at emitting a faithful projection.

**Sanity check performed 2026-08-10:** `which baml-cli` found nothing on
this environment's `PATH` — **skipped, not installed, no new dependency
added** to make the check pass (out of scope per L4). No `baml-cli`
round-trip was exercised; the guidance above documents the intended
integration, not a locally-verified BAML CLI run. Re-run the check on a
machine with `baml-cli` installed before relying on the CLI's exact
sub-command spelling.

## References

- Design: `doc/05_design/infra/llm/saml_baml_integration_research_design_plan_2026-08-09.md`
- Plan v1 (45 lanes, execution lanes now dropped): `doc/03_plan/infra/llm/saml_parallel_agents_plan_2026-08-09.md`
- Plan v2 (LSP-checked evidence, BAML-executed runtime — current): `doc/03_plan/infra/llm/saml_lsp_evidence_plan_2026-08-10.md`
- Research: `doc/01_research/infra/llm/saml_research_2026-08-09.md`
- LLM-process wiki: `doc/00_llm_process/feature_expert/saml/skill.md`
