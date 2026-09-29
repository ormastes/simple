# SCI-driven help + completion generation (Phase C / C4)

> Help text and shell-completion candidates are GENERATED from option-route

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SCI-driven help + completion generation (Phase C / C4)

Help text and shell-completion candidates are GENERATED from option-route

## At a Glance

| Field | Value |
|-------|-------|
| Category | Lib / Composition |
| Status | Acceptance (reproducing) |
| Source | `test/01_unit/lib/composition/cli_help_gen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Help text and shell-completion candidates are GENERATED from option-route
data — never hand-written. This spec builds route rows and asserts the real
registered options (spellings, aliases, value forms, summaries) appear in the
generated help index and completion output.

Struct rows are used directly (not class records) per
doc/08_tracking/bug/class_field_access_erased_under_test_runner_2026-08-18.md.

## Scenarios

### SCI-driven help index generation

#### renders every registered option with its summary

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders every registered option with its summary
- Generate the help index from three route rows
- Every real spelling and its route-carried summary is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders every registered option with its summary")
step("Generate the help index from three route rows")
val help = cli_help_index_render_v1(sample_routes())
step("Every real spelling and its route-carried summary is present")
expect(help.contains("--verbose")).to_be(true)
expect(help.contains("enable verbose output")).to_be(true)
expect(help.contains("--log-level=<value>")).to_be(true)
expect(help.contains("set log level")).to_be(true)
expect(help.contains("--color[=<value>]")).to_be(true)
```

</details>

#### derives usage forms from value_mode, not from hand-written text

- derives usage forms from value_mode, not from hand-written text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("derives usage forms from value_mode, not from hand-written text")
expect(cli_help_usage_form_v1("--a", CLI_VALUE_MODE_FLAG) == "--a").to_be(true)
expect(cli_help_usage_form_v1("--a", CLI_VALUE_MODE_REQUIRED) == "--a=<value>").to_be(true)
expect(cli_help_usage_form_v1("--a", CLI_VALUE_MODE_OPTIONAL) == "--a[=<value>]").to_be(true)
```

</details>

#### renders aliases and scope labels from the route data

- renders aliases and scope labels from the route data


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders aliases and scope labels from the route data")
val help = cli_help_index_render_v1(sample_routes())
expect(help.contains("(-v)")).to_be(true)
expect(help.contains("[global]")).to_be(true)
expect(help.contains("[command]")).to_be(true)
```

</details>

### shell completion generation from the same source

#### lists all spellings and aliases for the empty prefix

- lists all spellings and aliases for the empty prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lists all spellings and aliases for the empty prefix")
val cands = cli_completion_candidates_v1(sample_routes(), "")
expect(cands.len() == 4).to_be(true)
```

</details>

#### filters candidates by prefix including aliases

- filters candidates by prefix including aliases


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("filters candidates by prefix including aliases")
val dashdash = cli_completion_candidates_v1(sample_routes(), "--")
expect(dashdash.len() == 3).to_be(true)
val short = cli_completion_candidates_v1(sample_routes(), "-v")
expect(short.len() == 1).to_be(true)
expect(short[0] == "-v").to_be(true)
```

</details>

#### renders one candidate per line for compgen consumption

- renders one candidate per line for compgen consumption


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders one candidate per line for compgen consumption")
val rendered = cli_completion_render_v1(sample_routes(), "--")
expect(rendered.contains("--verbose\n")).to_be(true)
expect(rendered.contains("--log-level\n")).to_be(true)
expect(rendered.contains("--color\n")).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `969f0d31806b6da876f6639e48e3b2442b695f78b509998b669604d854f51527`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `969f0d31806b6da876f6639e48e3b2442b695f78b509998b669604d854f51527`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `969f0d31806b6da876f6639e48e3b2442b695f78b509998b669604d854f51527`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/composition/cli_help_gen_spec.spl
mirror: doc/06_spec/01_unit/lib/composition/cli_help_gen_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/composition/cli_help_gen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/composition/cli_help_gen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/composition/cli_help_gen_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders every registered option with its summary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/composition/cli_help_gen_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives usage forms from value_mode, not from hand-written text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/composition/cli_help_gen_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders aliases and scope labels from the route data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
