# Mir Eviction Hazards Specification

> Tests covering driver MIR eviction hazards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Eviction Hazards Specification

## Scenarios

### driver MIR eviction hazards

#### clears the bootstrap entry alias when the entry module is evicted

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- clears the bootstrap entry alias when the entry module is evicted
   - Expected: entry_alias_present(ctx) is true
   - Expected: ctx.mir_modules.has("app.cli.bootstrap_main") is false
   - Expected: entry_alias_present(ctx) is false
   - Expected: ctx.bootstrap_entry_mir_name equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears the bootstrap entry alias when the entry module is evicted")
var ctx = fresh_context()
val entry = empty_mir("app.cli.bootstrap_main")
ctx.mir_modules["app.cli.bootstrap_main"] = entry
ctx.set_bootstrap_entry_mir("app.cli.bootstrap_main", entry)
expect(entry_alias_present(ctx)).to_equal(true)

ctx.evict_mir_module("app.cli.bootstrap_main")

expect(ctx.mir_modules.has("app.cli.bootstrap_main")).to_equal(false)
# Before the fix this stayed Some(...) -- a logical alias naming an
# evicted module, which is exactly what hazard 1 describes.
expect(entry_alias_present(ctx)).to_equal(false)
expect(ctx.bootstrap_entry_mir_name).to_equal("")
```

</details>

#### keeps the bootstrap entry alias when a DIFFERENT module is evicted

- keeps the bootstrap entry alias when a DIFFERENT module is evicted
   - Expected: ctx.mir_modules.has("std.text") is false
   - Expected: ctx.mir_modules.has("app.cli.bootstrap_main") is true
   - Expected: entry_alias_present(ctx) is true
   - Expected: ctx.bootstrap_entry_mir_name equals `app.cli.bootstrap_main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the bootstrap entry alias when a DIFFERENT module is evicted")
var ctx = fresh_context()
val entry = empty_mir("app.cli.bootstrap_main")
ctx.mir_modules["app.cli.bootstrap_main"] = entry
ctx.mir_modules["std.text"] = empty_mir("std.text")
ctx.set_bootstrap_entry_mir("app.cli.bootstrap_main", entry)

ctx.evict_mir_module("std.text")

# Over-clearing would break the bootstrap native path, which reads the
# alias back after codegen. Only the entry's OWN eviction clears it.
expect(ctx.mir_modules.has("std.text")).to_equal(false)
expect(ctx.mir_modules.has("app.cli.bootstrap_main")).to_equal(true)
expect(entry_alias_present(ctx)).to_equal(true)
expect(ctx.bootstrap_entry_mir_name).to_equal("app.cli.bootstrap_main")
```

</details>

#### evicting a never-registered module leaves an unrelated alias alone

- evicting a never-registered module leaves an unrelated alias alone
   - Expected: entry_alias_present(ctx) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evicting a never-registered module leaves an unrelated alias alone")
var ctx = fresh_context()
val entry = empty_mir("app.cli.bootstrap_main")
ctx.mir_modules["app.cli.bootstrap_main"] = entry
ctx.set_bootstrap_entry_mir("app.cli.bootstrap_main", entry)

ctx.evict_mir_module("never.registered.module")

expect(entry_alias_present(ctx)).to_equal(true)
```

</details>

#### evict_hir still clears its own bootstrap entry twin

- evict_hir still clears its own bootstrap entry twin
   - Expected: ctx.hir_modules.has("app.cli.bootstrap_main") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evict_hir still clears its own bootstrap entry twin")
# The pattern hazard 1's fix mirrors. Guarded here so the two eviction
# paths cannot drift apart again.
var ctx = fresh_context()
ctx.evict_hir()
expect(ctx.hir_modules.has("app.cli.bootstrap_main")).to_equal(false)
```

</details>

#### disables MIR eviction under --output-format both

- disables MIR eviction under --output-format both
   - Expected: driver_mir_eviction_enabled(true, driver_output_format_both()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disables MIR eviction under --output-format both")
# hazard 3: `both` runs compile_to_smf AFTER compile_to_native over the
# same context, and compile_to_smf re-reads ctx.mir_modules.
expect(driver_mir_eviction_enabled(true, driver_output_format_both())).to_equal(false)
```

</details>

#### still evicts under --low-memory for every single-artifact format

- still evicts under --low-memory for every single-artifact format
   - Expected: driver_mir_eviction_enabled(true, driver_output_format_native()) is true
   - Expected: driver_mir_eviction_enabled(true, driver_output_format_smf()) is true
   - Expected: driver_mir_eviction_enabled(true, driver_output_format_self_contained()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still evicts under --low-memory for every single-artifact format")
expect(driver_mir_eviction_enabled(true, driver_output_format_native())).to_equal(true)
expect(driver_mir_eviction_enabled(true, driver_output_format_smf())).to_equal(true)
expect(driver_mir_eviction_enabled(true, driver_output_format_self_contained())).to_equal(true)
```

</details>

#### never evicts without --low-memory

- never evicts without --low-memory
   - Expected: driver_mir_eviction_enabled(false, driver_output_format_native()) is false
   - Expected: driver_mir_eviction_enabled(false, driver_output_format_smf()) is false
   - Expected: driver_mir_eviction_enabled(false, driver_output_format_both()) is false
   - Expected: driver_mir_eviction_enabled(false, driver_output_format_self_contained()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never evicts without --low-memory")
expect(driver_mir_eviction_enabled(false, driver_output_format_native())).to_equal(false)
expect(driver_mir_eviction_enabled(false, driver_output_format_smf())).to_equal(false)
expect(driver_mir_eviction_enabled(false, driver_output_format_both())).to_equal(false)
expect(driver_mir_eviction_enabled(false, driver_output_format_self_contained())).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/mir_eviction_hazards_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering driver MIR eviction hazards.
- driver MIR eviction hazards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `9dd00db2bae421f65205d29d647d566b4d930bc3d0e02f7cae80a6f154337672`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9dd00db2bae421f65205d29d647d566b4d930bc3d0e02f7cae80a6f154337672`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9dd00db2bae421f65205d29d647d566b4d930bc3d0e02f7cae80a6f154337672`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/mir_eviction_hazards_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/mir_eviction_hazards_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/mir_eviction_hazards_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/mir_eviction_hazards_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/mir_eviction_hazards_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clears the bootstrap entry alias when the entry module is evicted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/mir_eviction_hazards_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the bootstrap entry alias when a DIFFERENT module is evicted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/mir_eviction_hazards_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evicting a never-registered module leaves an unrelated alias alone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
