# Module Import New Submodule Specification

> Tests covering Module Import - Compiled-In Package.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Import New Submodule Specification

## Scenarios

### Module Import - Compiled-In Package

#### existing functions (baseline)

#### imports existing std.cli_output function via init

- imports existing std.cli_output function via init
   - Expected: _can_run is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("imports existing std.cli_output function via init")
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_and_check("baseline_init_import.spl", "baseline init import")
```

</details>

#### imports existing std.cli_output submodule directly

- imports existing std.cli_output submodule directly
   - Expected: _can_run is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("imports existing std.cli_output submodule directly")
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_and_check("baseline_direct_import.spl", "baseline direct import")
```

</details>

#### new submodule file in compiled-in package

#### can load new spl file without parse errors (run directly)

- can load new spl file without parse errors (run directly)
   - Expected: _can_run is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can load new spl file without parse errors (run directly)")
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_setup_probe_direct_and_check()
```

</details>

#### can import function from new submodule via direct path

- can import function from new submodule via direct path
   - Expected: _can_run is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can import function from new submodule via direct path")
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_setup_probe_and_check("probe_direct_import.spl", "New submodule direct import fails")
```

</details>

#### buffer.spl (the actual module we need)

#### can import buffer_start via direct submodule path

- can import buffer_start via direct submodule path
   - Expected: _can_run is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can import buffer_start via direct submodule path")
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_and_check_known_bug("buffer_direct_import.spl", "buffer.spl direct import fails")
```

</details>

#### can import log_print via direct submodule path

- can import log_print via direct submodule path
   - Expected: _can_run is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can import log_print via direct submodule path")
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_and_check_known_bug("buffer_logprint_import.spl", "buffer.spl log_print import fails")
```

</details>

#### can import buffer functions via init reexport

- can import buffer functions via init reexport
   - Expected: _can_run is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can import buffer functions via init reexport")
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_and_check_known_bug("buffer_init_import.spl", "buffer.spl init re-export fails")
```

</details>

#### fresh non-compiled package (control test)

#### can import from a completely new package via direct path

- can import from a completely new package via direct path
   - Expected: _can_run is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can import from a completely new package via direct path")
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_setup_fresh_and_check("fresh_pkg_direct_import.spl", "Fresh package direct import")
```

</details>

#### can import from a completely new package via init

- can import from a completely new package via init
   - Expected: _can_run is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can import from a completely new package via init")
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_setup_fresh_and_check("fresh_pkg_init_import.spl", "Fresh package init import")
```

</details>

#### module loading diagnostics

#### buffer.spl is found by resolver (not module-not-found)

- buffer.spl is found by resolver (not module-not-found)
   - Expected: _can_run is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("buffer.spl is found by resolver (not module-not-found)")
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_diag_module_loading()
```

</details>

#### extern fn in module does not prevent function registration

- extern fn in module does not prevent function registration
   - Expected: _can_run is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extern fn in module does not prevent function registration")
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_setup_probe_extern_and_check()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/module_import/module_import_new_submodule_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Module Import - Compiled-In Package.
- Module Import - Compiled-In Package

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `19f258337ab87aea6c58271cb0785ce744127fa895830aaa41752092518b5801`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `19f258337ab87aea6c58271cb0785ce744127fa895830aaa41752092518b5801`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `19f258337ab87aea6c58271cb0785ce744127fa895830aaa41752092518b5801`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/compiler/module_import/module_import_new_submodule_spec.spl
mirror: doc/06_spec/03_system/compiler/module_import/module_import_new_submodule_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/module_import/module_import_new_submodule_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/module_import/module_import_new_submodule_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/module_import/module_import_new_submodule_spec.spl:168:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports existing std.cli_output function via init' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/module_import/module_import_new_submodule_spec.spl:176:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports existing std.cli_output submodule directly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/module_import/module_import_new_submodule_spec.spl:190:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can load new spl file without parse errors (run directly)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/module_import/module_import_new_submodule_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can load new spl file without parse errors (run directly)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/module_import/module_import_new_submodule_spec.spl:198:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can import function from new submodule via direct path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/module_import/module_import_new_submodule_spec.spl:212:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can import buffer_start via direct submodule path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/module_import/module_import_new_submodule_spec.spl:220:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can import log_print via direct submodule path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/module_import/module_import_new_submodule_spec.spl:228:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can import buffer functions via init reexport' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/module_import/module_import_new_submodule_spec.spl:242:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can import from a completely new package via direct path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
