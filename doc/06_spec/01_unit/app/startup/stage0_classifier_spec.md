# stage0_classifier_spec

> Purpose: this manual pins the behavior named "stage-0 classifier maps representative invocations to their class" for the owning engineering team.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# stage0_classifier_spec

Purpose: this manual pins the behavior named "stage-0 classifier maps representative invocations to their class" for the owning engineering team.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/startup/stage0_classifier_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose: this manual pins the behavior named "stage-0 classifier maps representative invocations to their class" for the owning engineering team.
    Audience: engineers verifying regressions in this area; steps below are executable evidence.

## Scenarios

### stage-0 classifier maps representative invocations to their class

#### empty argv is the root default policy

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- empty argv is the root default policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("empty argv is the root default policy")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
assert_eq(stage0_classify([]), stage0_class_root_default())
```

</details>

#### -h and --help classify as help

- -h and --help classify as help


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("-h and --help classify as help")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
assert_eq(stage0_classify(["-h"]), stage0_class_help())
assert_eq(stage0_classify(["--help"]), stage0_class_help())
```

</details>

#### -v and --version classify as version

- -v and --version classify as version


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("-v and --version classify as version")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
assert_eq(stage0_classify(["-v"]), stage0_class_version())
assert_eq(stage0_classify(["--version"]), stage0_class_version())
```

</details>

#### source extensions classify as run_source

- source extensions classify as run_source


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("source extensions classify as run_source")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
assert_eq(stage0_classify(["app/main.spl"]), stage0_class_run_source())
assert_eq(stage0_classify(["tool.shs", "--flag"]), stage0_class_run_source())
assert_eq(stage0_classify(["m.simple"]), stage0_class_run_source())
assert_eq(stage0_classify(["s.sscript"]), stage0_class_run_source())
```

</details>

#### .smf artifacts classify as smf_artifact

- .smf artifacts classify as smf_artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step(".smf artifacts classify as smf_artifact")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
assert_eq(stage0_classify(["build/out.smf"]), stage0_class_smf_artifact())
```

</details>

#### explicit paths without artifact extension classify as native_exec

- explicit paths without artifact extension classify as native_exec


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("explicit paths without artifact extension classify as native_exec")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
assert_eq(stage0_classify(["./mybin"]), stage0_class_native_exec())
assert_eq(stage0_classify(["/usr/bin/thing", "arg"]), stage0_class_native_exec())
assert_eq(stage0_classify(["../rel/bin"]), stage0_class_native_exec())
```

</details>

#### CLI-0 run and test commands get their own classes

- CLI-0 run and test commands get their own classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("CLI-0 run and test commands get their own classes")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
assert_eq(stage0_classify(["run", "app/main.spl"]), stage0_class_command_run())
assert_eq(stage0_classify(["test", "test/x_spec.spl"]), stage0_class_command_test())
```

</details>

#### --x namespace options classify by shape only

- --x namespace options classify by shape only


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("--x namespace options classify by shape only")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
assert_eq(stage0_classify(["--xlog.level=debug"]), stage0_class_namespace_option())
```

</details>

#### other leading options route to the SCI exact-option lookup

- other leading options route to the SCI exact-option lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("other leading options route to the SCI exact-option lookup")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
assert_eq(stage0_classify(["--some-generated-option"]), stage0_class_option_route())
assert_eq(stage0_classify(["-q"]), stage0_class_option_route())
```

</details>

#### other bare command words route to SCI

- other bare command words route to SCI


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("other bare command words route to SCI")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
assert_eq(stage0_classify(["compile", "x.spl"]), stage0_class_sci_route())
```

</details>

#### hard -- terminator forces positional classification

- hard -- terminator forces positional classification


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("hard -- terminator forces positional classification")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
assert_eq(stage0_classify(["--", "app/main.spl"]), stage0_class_run_source())
assert_eq(stage0_classify(["--", "--help"]), stage0_class_sci_route())
assert_eq(stage0_classify(["--"]), stage0_class_unknown())
```

</details>

#### empty token is unknown

- empty token is unknown


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("empty token is unknown")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
assert_eq(stage0_classify([""]), stage0_class_unknown())
```

</details>

#### class names are stable diagnostics labels

- class names are stable diagnostics labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("class names are stable diagnostics labels")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
assert_eq(stage0_class_name(stage0_class_help()), "help")
assert_eq(stage0_class_name(stage0_class_version()), "version")
assert_eq(stage0_class_name(stage0_class_command_test()), "command_test")
assert_eq(stage0_class_name(stage0_class_unknown()), "unknown")
assert_eq(stage0_class_name(999), "unknown")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ab239f0ca908b7064df841b28161ded5f7b6494c2e367fcad4133ee84f27630a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab239f0ca908b7064df841b28161ded5f7b6494c2e367fcad4133ee84f27630a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab239f0ca908b7064df841b28161ded5f7b6494c2e367fcad4133ee84f27630a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/app/startup/stage0_classifier_spec.spl
mirror: doc/06_spec/01_unit/app/startup/stage0_classifier_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/startup/stage0_classifier_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/startup/stage0_classifier_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
