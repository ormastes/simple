# Precise entry-script detection in app.cli_util

> `app.cli_util.get_cli_args` used to decide whether argv[1] was the interpreted

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Precise entry-script detection in app.cli_util

`app.cli_util.get_cli_args` used to decide whether argv[1] was the interpreted

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli_util_entry_script_precise_predicate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

`app.cli_util.get_cli_args` used to decide whether argv[1] was the interpreted
entry script with a bare `ends_with("main.spl")` test. A compiled application
whose own first argument legitimately ends in `main.spl` (for example
`simple check-dbs build/h_main.spl`) had that argument silently swallowed.

The precise form takes the application's own entry path and matches it exactly
(bare, `src/`-prefixed, or as a trailing path component), so an unrelated user
argument ending in `main.spl` is never mistaken for the entry script.

## Scenarios

### cli_util precise entry-script predicate

#### no longer decides entry-script-ness by a bare main.spl suffix

- no longer decides entry-script-ness by a bare main.spl suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no longer decides entry-script-ness by a bare main.spl suffix")
val source = cli_util_source()
assert_false(source.contains("ends_with(\"main.spl\")"))
```

</details>

#### exposes a path-parameterised entry-script predicate

- exposes a path-parameterised entry-script predicate


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes a path-parameterised entry-script predicate")
val source = cli_util_source()
expect(source).to_contain("fn arg_is_entry_script(arg: text, entry_rel: text) -> bool")
expect(source).to_contain("export arg_is_entry_script, strip_entry_script")
```

</details>

#### exposes a pure, testable argument-stripping helper

- exposes a pure, testable argument-stripping helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes a pure, testable argument-stripping helper")
val source = cli_util_source()
expect(source).to_contain("fn strip_entry_script(raw: [text], entry_rel: text) -> [text]")
expect(source).to_contain("export arg_is_entry_script, strip_entry_script")
```

</details>

#### requires each caller to name its own entry script

- requires each caller to name its own entry script


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires each caller to name its own entry script")
val source = cli_util_source()
expect(source).to_contain("fn get_cli_args(entry_rel: text) -> [text]")
```

</details>

#### keeps the live consumers passing their own entry path

- keeps the live consumers passing their own entry path


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the live consumers passing their own entry path")
val check_dbs = rt_file_read_text("src/app/check_dbs/main.spl") ?? ""
expect(check_dbs).to_contain("get_cli_args(\"app/check_dbs/main.spl\")")
# ffi_gen/test_all_mods.spl imported get_cli_args but never called it;
# the unused import is gone rather than carried through the signature change.
val ffi_gen = rt_file_read_text("src/app/ffi_gen/test_all_mods.spl") ?? ""
assert_false(ffi_gen.contains("get_cli_args"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `4bc471a2f9fd13f8caa3fc6e4b12c67703a4721932537d5acaac0a8ec3384f0d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4bc471a2f9fd13f8caa3fc6e4b12c67703a4721932537d5acaac0a8ec3384f0d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4bc471a2f9fd13f8caa3fc6e4b12c67703a4721932537d5acaac0a8ec3384f0d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/cli_util_entry_script_precise_predicate_spec.spl
mirror: doc/06_spec/01_unit/app/cli_util_entry_script_precise_predicate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli_util_entry_script_precise_predicate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli_util_entry_script_precise_predicate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli_util_entry_script_precise_predicate_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no longer decides entry-script-ness by a bare main.spl suffix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli_util_entry_script_precise_predicate_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes a path-parameterised entry-script predicate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli_util_entry_script_precise_predicate_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes a pure, testable argument-stripping helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
