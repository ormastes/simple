# Native Build Arg Source Specification

> Tests covering native-build CLI arg source regressions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Build Arg Source Specification

## Scenarios

### native-build CLI arg source regressions

#### routes omitted --backend through the default Simple LLVM backend

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes omitted --backend through the default Simple LLVM backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes omitted --backend through the default Simple LLVM backend")
val source = file_read("src/app/cli/_CliMain/main_and_help.spl")
expect(source).to_contain("not saw_backend")
```

</details>

#### does not treat malformed --backend as omitted

- does not treat malformed --backend as omitted
   - Expected: source does not contain `arg == "--backend"`
   - Expected: source does not contain `backend == "llvm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not treat malformed --backend as omitted")
val source = file_read("src/app/cli/_CliMain/main_and_help.spl")
expect(source).to_contain("fn native_build_backend_supported(backend: text) -> bool:")
expect(source).to_contain("if str_eq(arg, \"--backend\"):")
expect(source).to_contain("return native_build_backend_supported(args[i + 1])")
expect(source).to_contain("return false")
expect(source.contains("arg == \"--backend\"")).to_equal(false)
expect(source.contains("backend == \"llvm")).to_equal(false)
```

</details>

#### matches native-build command exactly

- matches native-build command exactly
   - Expected: source does not contain `args[0].starts_with("native-build")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("matches native-build command exactly")
val source = file_read("src/app/cli/_CliMain/main_and_help.spl")
expect(source).to_contain("str_eq(args[0], \"native-build\")")
expect(source.contains("args[0].starts_with(\"native-build\")")).to_equal(false)
```

</details>

#### keeps native_build_main option checks off raw string equality

- keeps native_build_main option checks off raw string equality
   - Expected: source does not contain `raw_args[i] == "native-build"`
   - Expected: source does not contain `args[i] == "--timeout"`
   - Expected: source does not contain `a == "-o"`
   - Expected: source does not contain `"args`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps native_build_main option checks off raw string equality")
val source = file_read("src/app/cli/native_build_main.spl")
expect(source).to_contain("native_build_text_eq(raw_args[i], \"native-build\")")
expect(source).to_contain("native_build_text_eq(args[i], \"--timeout\")")
expect(source).to_contain("native_build_text_eq(a, \"-o\")")
expect(source).to_contain("native_build_text_eq(a, \"--output\")")
expect(source).to_contain("fn native_build_has_help(args: [text]) -> bool:")
expect(source.contains("raw_args[i] == \"native-build\"")).to_equal(false)
expect(source.contains("args[i] == \"--timeout\"")).to_equal(false)
expect(source.contains("a == \"-o\"")).to_equal(false)
expect(source.contains("args.contains(\"-h\")")).to_equal(false)
```

</details>

#### matches only --entry and --entry=value for native-build entry parsing

- matches only --entry and --entry=value for native-build entry parsing
   - Expected: source does not contain `elif a.starts_with("--entry")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("matches only --entry and --entry=value for native-build entry parsing")
val source = file_read("src/app/io/_CliCompile/compile_targets.spl")
expect(source).to_contain("arg == \"--entry\" or arg.starts_with(\"--entry=\")")
expect(source.contains("elif a.starts_with(\"--entry\")")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/native_build_arg_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native-build CLI arg source regressions.
- native-build CLI arg source regressions

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
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3554b1385653b04ef6067be0fbcd2ef3f79581220c1c2aa73b1f2e10f63d4ebf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3554b1385653b04ef6067be0fbcd2ef3f79581220c1c2aa73b1f2e10f63d4ebf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3554b1385653b04ef6067be0fbcd2ef3f79581220c1c2aa73b1f2e10f63d4ebf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/cli/native_build_arg_source_spec.spl
mirror: doc/06_spec/01_unit/app/cli/native_build_arg_source_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/app/cli/native_build_arg_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/native_build_arg_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/native_build_arg_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/cli/native_build_arg_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/cli/native_build_arg_source_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes omitted --backend through the default Simple LLVM backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/native_build_arg_source_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not treat malformed --backend as omitted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/native_build_arg_source_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches native-build command exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
