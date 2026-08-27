# Lazy Module Loader Bridge (W2-A2, AC-4 smoke)

> Drives src/compiler/10.frontend/core/interpreter/module_loader_lazy.spl

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lazy Module Loader Bridge (W2-A2, AC-4 smoke)

Drives src/compiler/10.frontend/core/interpreter/module_loader_lazy.spl

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/module_loader_lazy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Drives src/compiler/10.frontend/core/interpreter/module_loader_lazy.spl
directly (no load_module wiring needed):
- outline scan of real modules records the declaration surface only,
- the module is registered through the existing deferred mechanism
  (so the first symbol use materializes it via try_force_any_deferred_for),
- per-function body spans slice back to the exact function source text that
  the materializer parses on first call.

Each scenario runs inside a module-level helper returning "" on success or
an error description; the it blocks assert on that single value. (In
interpreter mode, `it` closures observe stale module state and expects on
non-local expressions can be hollow, so all stateful work happens in
ordinary functions.)

NOTE: actually running the self-hosted parser/eval (force -> load_module ->
parse) is not possible from interpreter-mode specs (same limitation as
test/02_integration/compiler/core_interpreter_intensive_spec.spl); the full
load-equivalence and benchmark coverage is task W2-A1 in compiled mode.

## Scenarios

### lazy module loader bridge

#### outline-scans a real module and defers it with its declaration surface

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- outline-scans a real module and defers it with its declaration surface
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outline-scans a real module and defers it with its declaration surface")
val err = check_defers_ctype()
expect(err).to_equal("")
```

</details>

#### records body spans that slice to the exact function source

- records body spans that slice to the exact function source
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records body spans that slice to the exact function source")
val err = check_slice_to_upper()
expect(err).to_equal("")
```

</details>

#### scans a module with docstrings and quote-heavy literal bodies

- scans a module with docstrings and quote-heavy literal bodies
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scans a module with docstrings and quote-heavy literal bodies")
val err = check_text_advanced()
expect(err).to_equal("")
```

</details>

#### keeps the default mode gates off

- keeps the default mode gates off
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the default mode gates off")
val err = check_mode_gates()
expect(err).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `26b6b19c3df6d597e577d422f3344a364fd0cbc12b5a9e1c2b3a40181359a1f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26b6b19c3df6d597e577d422f3344a364fd0cbc12b5a9e1c2b3a40181359a1f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26b6b19c3df6d597e577d422f3344a364fd0cbc12b5a9e1c2b3a40181359a1f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/module_loader_lazy_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/module_loader_lazy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/module_loader_lazy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/module_loader_lazy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/module_loader_lazy_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'outline-scans a real module and defers it with its declaration surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/module_loader_lazy_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records body spans that slice to the exact function source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/module_loader_lazy_spec.spl:165:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scans a module with docstrings and quote-heavy literal bodies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
