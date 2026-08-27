# Module Loader Crash Fix Specification

> Tests covering Module Loader Crash Fix.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Loader Crash Fix Specification

## Scenarios

### Module Loader Crash Fix

#### exposes safe method-based constructor functions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes safe method-based constructor functions
   - Expected: config.enable_jit is true
   - Expected: loader.config.max_cache_size equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes safe method-based constructor functions")
val config = ModuleLoaderConfig.default()
val loader = ModuleLoader.new(config)

expect(config.enable_jit).to_equal(true)
expect(loader.config.max_cache_size).to_equal(100)
```

</details>

#### supports reload without recursive unload failures

- supports reload without recursive unload failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports reload without recursive unload failures")
var loader = ModuleLoader.with_defaults()
val missing = moduleloader_reload(loader, "test/unit/compiler/loader/missing_for_reload.spl")

match missing:
    case LoadResult.Error(message):
        expect(message).to_contain("module not found")
    case _:
        fail("expected reload error for missing path")
```

</details>

#### allows unloading an unknown path safely

- allows unloading an unknown path safely
   - Expected: loader.stats().module_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows unloading an unknown path safely")
var loader = ModuleLoader.with_defaults()
moduleloader_unload(loader, "test/unit/compiler/loader/unknown_path.spl")
expect(loader.stats().module_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/loader/module_loader_crash_fix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Module Loader Crash Fix.
- Module Loader Crash Fix

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c578ed0c1d8c7cf485878ad4836f1bbed5853c34bedd55f71ec314bd3a9fdd3b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c578ed0c1d8c7cf485878ad4836f1bbed5853c34bedd55f71ec314bd3a9fdd3b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c578ed0c1d8c7cf485878ad4836f1bbed5853c34bedd55f71ec314bd3a9fdd3b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/loader/module_loader_crash_fix_spec.spl
mirror: doc/06_spec/unit/compiler/loader/module_loader_crash_fix_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/loader/module_loader_crash_fix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/loader/module_loader_crash_fix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/loader/module_loader_crash_fix_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/loader/module_loader_crash_fix_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes safe method-based constructor functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/loader/module_loader_crash_fix_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports reload without recursive unload failures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/loader/module_loader_crash_fix_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows unloading an unknown path safely' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
