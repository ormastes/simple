# Module Path Naming Specification

> Tests covering module_logical_name_from_path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Path Naming Specification

## Scenarios

### module_logical_name_from_path

#### strips a leading src/ and the .spl extension

- strips a leading src/ and the .spl extension
   - Expected: module_logical_name_from_path("src/_wallB_mod_a.spl") equals `_wallB_mod_a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips a leading src/ and the .spl extension")
expect(module_logical_name_from_path("src/_wallB_mod_a.spl")).to_equal("_wallB_mod_a")
```

</details>

#### dots nested directory separators

- dots nested directory separators
   - Expected: module_logical_name_from_path("src/compiler/foo/bar.spl") equals `compiler.foo.bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dots nested directory separators")
expect(module_logical_name_from_path("src/compiler/foo/bar.spl")).to_equal("compiler.foo.bar")
```

</details>

#### keeps an absolute path repo-relative by cutting at /src/

- keeps an absolute path repo-relative by cutting at /src/
   - Expected: module_logical_name_from_path("/home/u/work/simple/src/app/cli/main.spl") equals `app.cli.main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps an absolute path repo-relative by cutting at /src/")
expect(module_logical_name_from_path("/home/u/work/simple/src/app/cli/main.spl")).to_equal("app.cli.main")
```

</details>

#### normalizes backslashes before cutting at /src/

- normalizes backslashes before cutting at /src/
   - Expected: module_logical_name_from_path("C:\\work\\simple\\src\\app\\cli\\main.spl") equals `app.cli.main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes backslashes before cutting at /src/")
expect(module_logical_name_from_path("C:\\work\\simple\\src\\app\\cli\\main.spl")).to_equal("app.cli.main")
```

</details>

#### strips leading ./ and ../ segments

- strips leading ./ and ../ segments
   - Expected: module_logical_name_from_path("../../src/lib/text.spl") equals `lib.text`
   - Expected: module_logical_name_from_path("./src/lib/text.spl") equals `lib.text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips leading ./ and ../ segments")
expect(module_logical_name_from_path("../../src/lib/text.spl")).to_equal("lib.text")
expect(module_logical_name_from_path("./src/lib/text.spl")).to_equal("lib.text")
```

</details>

#### keeps the examples/ segment when there is no /src/

- keeps the examples/ segment when there is no /src/
   - Expected: module_logical_name_from_path("/home/u/simple/examples/demo.spl") equals `examples.demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the examples/ segment when there is no /src/")
expect(module_logical_name_from_path("/home/u/simple/examples/demo.spl")).to_equal("examples.demo")
```

</details>

#### sanitizes host-path punctuation into underscores

- sanitizes host-path punctuation into underscores
   - Expected: module_logical_name_from_path("/tmp/probe-dir/entry.spl") equals `.tmp.probe_dir.entry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sanitizes host-path punctuation into underscores")
# A path with neither /src/ nor /examples/ keeps its leading "/",
# which the "/" -> "." rewrite turns into a leading dot. Pinned as-is:
# this is the shape the entry_main_symbol comparison actually sees for
# out-of-tree entries, so it must not change silently.
expect(module_logical_name_from_path("/tmp/probe-dir/entry.spl")).to_equal(".tmp.probe_dir.entry")
```

</details>

#### strips the .sdn extension too

- strips the .sdn extension too
   - Expected: module_logical_name_from_path("src/config/app.sdn") equals `config.app`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips the .sdn extension too")
expect(module_logical_name_from_path("src/config/app.sdn")).to_equal("config.app")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/common/module_path_naming_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering module_logical_name_from_path.
- module_logical_name_from_path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `eb630896227204d33b2f1f26070f6cca14a787d934860a7a7a716a17778a233e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb630896227204d33b2f1f26070f6cca14a787d934860a7a7a716a17778a233e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb630896227204d33b2f1f26070f6cca14a787d934860a7a7a716a17778a233e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/common/module_path_naming_spec.spl
mirror: doc/06_spec/01_unit/compiler/common/module_path_naming_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/common/module_path_naming_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/common/module_path_naming_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/common/module_path_naming_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'strips a leading src/ and the .spl extension' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/common/module_path_naming_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dots nested directory separators' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/common/module_path_naming_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps an absolute path repo-relative by cutting at /src/' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
