# cli_args_modspl_spec

> Purpose: a cli block embedded in a module entry point is observed through the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cli_args_modspl_spec

Purpose: a cli block embedded in a module entry point is observed through the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | Active |
| Source | `test/feature/usage/cli_args_modspl_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: a cli block embedded in a module entry point is observed through the
production parser — the module's program identity propagates into generated
help, module-declared options parse from argv, and the cli surface stays
composable with module functions. Audience: CLI/language engineers.

## Scenarios

### CLI Args mod.spl Embedding

#### module entry point

#### module cli keeps its program identity in generated help

- Verify: program name and description surface in help


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: program name and description surface in help")
val help = generate_help(module_entry_cli())
expect(help).to_contain("my_tool")  # oracle: module name is the program name
expect(help).to_contain("module entry point cli")  # oracle: module description surfaces
```

</details>

#### module interaction

#### module-declared flags and options parse from argv

- Verify: -v and --output both resolve through the module cli
   - Expected: parsed_flag(parsed, "verbose") is true
   - Expected: parsed_option(parsed, "output") equals `result.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: -v and --output both resolve through the module cli")
val parsed = parse_cli_args(module_entry_cli(), ["-v", "--output=result.txt"])
expect(parsed_flag(parsed, "verbose")).to_equal(true)  # oracle: short flag parsed
expect(parsed_option(parsed, "output")).to_equal("result.txt")  # oracle: long option parsed
```

</details>

#### module cli defaults hold when argv is empty

- Verify: defaults survive without arguments
   - Expected: parsed_flag(parsed, "verbose") is false
   - Expected: parsed_option(parsed, "output") equals `out.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: defaults survive without arguments")
val parsed = parse_cli_args(module_entry_cli(), [])
expect(parsed_flag(parsed, "verbose")).to_equal(false)  # oracle: flag default false
expect(parsed_option(parsed, "output")).to_equal("out.txt")  # oracle: option default retained
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c45b33bbc7cda617aedab755f3be01760afb34161816fbc66edcc9ccd9b6fe21`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c45b33bbc7cda617aedab755f3be01760afb34161816fbc66edcc9ccd9b6fe21`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c45b33bbc7cda617aedab755f3be01760afb34161816fbc66edcc9ccd9b6fe21`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/cli_args_modspl_spec.spl
mirror: doc/06_spec/feature/usage/cli_args_modspl_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/cli_args_modspl_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/cli_args_modspl_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/cli_args_modspl_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'module cli keeps its program identity in generated help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cli_args_modspl_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'module-declared flags and options parse from argv' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cli_args_modspl_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'module cli defaults hold when argv is empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
