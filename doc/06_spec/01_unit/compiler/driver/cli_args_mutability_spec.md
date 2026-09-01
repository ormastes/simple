# Contract spec: test/01_unit/compiler/driver/cli_args_mutability_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/driver/cli_args_mutability_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/cli_args_mutability_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/driver/cli_args_mutability_spec.spl` and a green Results line.

## Scenarios

### compiler driver CLI args mutability

#### marks mutating legacy opt-level helper as me

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- marks mutating legacy opt-level helper as me


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("marks mutating legacy opt-level helper as me")
val source = file_read("src/compiler/80.driver/main.spl")

expect(source).to_contain("me apply_legacy_opt_level(level: i64):")
expect(source).to_contain("me parse_long_option(arg: text, mut result: CliArgs)")
expect(source).to_contain("fn apply_option(name: text, value: text, mut result: CliArgs)")
expect(source).to_contain("me parse_short_option(arg: text, mut result: CliArgs)")
expect(source).to_not_contain("fn apply_legacy_opt_level(level: i64):")        expect(source).to_not_contain("val arg = if val next_arg = self.next()")        expect(source).to_not_contain("val file = if val next_file = self.next()")        expect(source).to_not_contain("= if val")
```

</details>

#### transports standalone mode as text past aggregate copies

- transports standalone mode as text past aggregate copies


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("transports standalone mode as text past aggregate copies")
val main_source = file_read("src/compiler/80.driver/main.spl")
# Repointed 2026-08-21: compile-mode dispatch moved to
# driver_orchestration.spl in the driver.spl split (4b88aebf00b).
val driver_source = file_read("src/compiler/80.driver/driver_orchestration.spl")
val types_source = file_read("src/compiler/80.driver/driver_types.spl")
val options_source = file_read("src/compiler/00.common/driver_core_types.spl")

expect(main_source).to_contain("options.cli_mode_text = requested_mode_text")
expect(main_source).to_not_contain("options.build_mode =")        expect(options_source).to_contain("    cli_mode_text: text\n")
expect(options_source).to_not_contain("cli_mode_text: text =")
expect(options_source).to_contain("cli_mode_text: opts.cli_mode_text")
expect(main_source).to_contain("elif arg == \"-m\" or arg == \"--mode\":")
expect(main_source).to_contain("Error: Unknown mode:")
expect(main_source).to_contain("requested_mode_text = _canonical_compile_mode_text(text)")
expect(types_source).to_contain("val backend = if selected_mode_text == \"interpret\"")
expect(driver_source).to_contain("compile_mode_text = self.ctx.options.cli_mode_text")
expect(driver_source).to_contain("if compile_mode_text == \"aot\":")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2b002218a411bf68c9c8dda987d3404c2fe71ede3d3be1b8121702e49e205c70`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2b002218a411bf68c9c8dda987d3404c2fe71ede3d3be1b8121702e49e205c70`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2b002218a411bf68c9c8dda987d3404c2fe71ede3d3be1b8121702e49e205c70`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/compiler/driver/cli_args_mutability_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/cli_args_mutability_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/driver/cli_args_mutability_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks mutating legacy opt-level helper as me' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/cli_args_mutability_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'transports standalone mode as text past aggregate copies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
