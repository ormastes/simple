# Defect class: argv entry-script detection by bare filename suffix

> The recurring defect is not one call site. It is the PATTERN of deciding

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Defect class: argv entry-script detection by bare filename suffix

The recurring defect is not one call site. It is the PATTERN of deciding

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/argv_entry_script_suffix_heuristic_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The recurring defect is not one call site. It is the PATTERN of deciding
"argv[1] is the interpreted entry script" from a bare filename suffix such as
`ends_with("main.spl")`. Under a compiled application any user argument that
happens to end in that suffix is swallowed and the command misroutes.

This spec scans owned application source for the pattern so a reintroduction
anywhere fails, not merely a regression at the one site that was fixed.
Precise predicates match a full entry path (`arg_is_cli_entry_script`,
`arg_is_entry_script`) and are unaffected.

## Scenarios

### defect class: argv entry-script suffix heuristic

#### control: the detector fires on the defective shape and not on prose

- control: the detector fires on the defective shape and not on prose


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("control: the detector fires on the defective shape and not on prose")
# Without this, a clean sweep could mean the detector is broken.
assert_true(detects("    if all_args[1].ends_with(\"main.spl\"):"))
assert_false(detects("    # if arg.ends_with(\"main.spl\") is the anti-pattern"))
assert_false(detects("    if arg.ends_with(\"/app/cli/main.spl\"):"))
```

</details>

#### control: the scan can see the files it claims to scan

- control: the scan can see the files it claims to scan


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("control: the scan can see the files it claims to scan")
# Guards against an absence check that silently scanned nothing.
expect(source_of("src/app/cli_util.spl")).to_contain("fn get_cli_args")
expect(source_of("src/app/cli/_CliMain/args_and_os_commands.spl")).to_contain("arg_is_cli_entry_script")
```

</details>

#### app.cli_util does not detect the entry script by bare suffix

- app.cli_util does not detect the entry script by bare suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("app.cli_util does not detect the entry script by bare suffix")
assert_false(has_bare_suffix_heuristic("src/app/cli_util.spl"))
```

</details>

#### the CLI entry does not detect the entry script by bare suffix

- the CLI entry does not detect the entry script by bare suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the CLI entry does not detect the entry script by bare suffix")
assert_false(has_bare_suffix_heuristic("src/app/cli/_CliMain/args_and_os_commands.spl"))
```

</details>

#### the live cli_util consumers do not re-roll the heuristic themselves

- the live cli_util consumers do not re-roll the heuristic themselves


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the live cli_util consumers do not re-roll the heuristic themselves")
assert_false(has_bare_suffix_heuristic("src/app/check_dbs/main.spl"))
assert_false(has_bare_suffix_heuristic("src/app/ffi_gen/test_all_mods.spl"))
```

</details>

#### the precise predicates match a full entry path, not a filename

- the precise predicates match a full entry path, not a filename


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the precise predicates match a full entry path, not a filename")
val cli = source_of("src/app/cli/_CliMain/args_and_os_commands.spl")
expect(cli).to_contain("ends_with(\"/app/cli/main.spl\")")
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e1bb0b239c4f8e06761340e82601927aefa228cd3a615c93e3d7737ed835e29`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e1bb0b239c4f8e06761340e82601927aefa228cd3a615c93e3d7737ed835e29`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e1bb0b239c4f8e06761340e82601927aefa228cd3a615c93e3d7737ed835e29`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/argv_entry_script_suffix_heuristic_class_spec.spl
mirror: doc/06_spec/01_unit/app/argv_entry_script_suffix_heuristic_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/argv_entry_script_suffix_heuristic_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/argv_entry_script_suffix_heuristic_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/argv_entry_script_suffix_heuristic_class_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'control: the detector fires on the defective shape and not on prose' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/argv_entry_script_suffix_heuristic_class_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'control: the scan can see the files it claims to scan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/argv_entry_script_suffix_heuristic_class_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'app.cli_util does not detect the entry script by bare suffix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
