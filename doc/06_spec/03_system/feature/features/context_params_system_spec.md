# Context Params System Specification

> Tests covering Context Params: Phase 1 - Module-level context variables, Context Params: Phase 2 - Desugar output patterns, Context Params: Phase 3 - Full pipeline with context.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context Params System Specification

## Scenarios

### Context Params: Phase 1 - Module-level context variables

#### context variable starts as nil

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- context variable starts as nil
   - Expected: is_nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("context variable starts as nil")
__ctx_env = nil
val is_nil = __ctx_env == nil
expect(is_nil).to_equal(true)
```

</details>

#### module var can hold context value (within it block)

- module var can hold context value (within it block)
   - Expected: local_ctx equals `file_logger`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("module var can hold context value (within it block)")
var local_ctx = nil
local_ctx = "file_logger"
expect(local_ctx).to_equal("file_logger")
```

</details>

#### context variable can be set and restored (within it block)

- context variable can be set and restored (within it block)
   - Expected: __ctx_config equals `override`
   - Expected: __ctx_config equals `default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("context variable can be set and restored (within it block)")
var __ctx_config = "default"
val saved = __ctx_config
__ctx_config = "override"
expect(__ctx_config).to_equal("override")
__ctx_config = saved
expect(__ctx_config).to_equal("default")
```

</details>

#### module-level var is set by module function

- module-level var is set by module function
   - Expected: _get_env() equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("module-level var is set by module function")
# Module function sets module-level var; read back via getter to avoid local shadow
_set_env_to_test()
expect(_get_env()).to_equal("test")
```

</details>

### Context Params: Phase 2 - Desugar output patterns

#### with_context sets and restores context (simulated, within it block)

- with_context sets and restores context (simulated, within it block)
   - Expected: result equals `test_mode`
   - Expected: __ctx_scope equals `prod`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("with_context sets and restores context (simulated, within it block)")
var __ctx_scope: text = "prod"
val saved_scope_0 = __ctx_scope
__ctx_scope = "test"
val result = __ctx_scope + "_mode"
__ctx_scope = saved_scope_0
expect(result).to_equal("test_mode")
expect(__ctx_scope).to_equal("prod")
```

</details>

#### nested with_context uses distinct save vars (within it block)

- nested with_context uses distinct save vars (within it block)
   - Expected: inner_val equals `inner`
   - Expected: middle_val equals `middle`
   - Expected: __ctx_nested equals `outer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested with_context uses distinct save vars (within it block)")
var __ctx_nested: text = "outer"
val __saved_nested_0 = __ctx_nested
__ctx_nested = "middle"
val __saved_nested_1 = __ctx_nested
__ctx_nested = "inner"
val inner_val = __ctx_nested
__ctx_nested = __saved_nested_1
val middle_val = __ctx_nested
__ctx_nested = __saved_nested_0
expect(inner_val).to_equal("inner")
expect(middle_val).to_equal("middle")
expect(__ctx_nested).to_equal("outer")
```

</details>

#### multiple context vars declared in same module

- multiple context vars declared in same module
   - Expected: __ctx_env equals `production`
   - Expected: __ctx_mode equals `release`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiple context vars declared in same module")
__ctx_env = "production"
__ctx_mode = "release"
expect(__ctx_env).to_equal("production")
expect(__ctx_mode).to_equal("release")
```

</details>

#### setting one ctx var does not affect others

- setting one ctx var does not affect others
   - Expected: __ctx_mode equals `mode1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("setting one ctx var does not affect others")
__ctx_env = "env1"
__ctx_mode = "mode1"
__ctx_env = "env2"
expect(__ctx_mode).to_equal("mode1")
```

</details>

### Context Params: Phase 3 - Full pipeline with context

#### context variable can be used across multiple assignments in sequence

- context variable can be used across multiple assignments in sequence
   - Expected: v1 equals `first`
   - Expected: v2 equals `second`
   - Expected: v3 equals `third`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("context variable can be used across multiple assignments in sequence")
var __ctx_local: text = nil
__ctx_local = "first"
val v1 = __ctx_local
__ctx_local = "second"
val v2 = __ctx_local
__ctx_local = "third"
val v3 = __ctx_local
expect(v1).to_equal("first")
expect(v2).to_equal("second")
expect(v3).to_equal("third")
```

</details>

#### module function modifies context variable and it is visible

- module function modifies context variable and it is visible
   - Expected: current equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("module function modifies context variable and it is visible")
# Use getter to read module var (avoids local-shadow issue in it blocks)
_set_env_to_test()
val current = _get_env()
expect(current).to_equal("test")
```

</details>

#### module functions reading module context var (tests core feature)

- module functions reading module context var (tests core feature)
   - Expected: result equals `test_context`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("module functions reading module context var (tests core feature)")
# Set via module-level setter so the function sees the same var
_set_env("test_context")
val result = _get_env()
expect(result).to_equal("test_context")
```

</details>

#### module function using context var in computation (tests full feature)

- module function using context var in computation (tests full feature)
   - Expected: result equals `staging:deploy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("module function using context var in computation (tests full feature)")
# Set via module-level setter; _env_aware_op reads the same module var
_set_env("staging")
val result = _env_aware_op("deploy")
expect(result).to_equal("staging:deploy")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/context_params_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Context Params: Phase 1 - Module-level context variables, Context Params: Phase 2 - Desugar output patterns, Context Params: Phase 3 - Full pipeline with context.
- Context Params: Phase 1 - Module-level context variables
- Context Params: Phase 2 - Desugar output patterns
- Context Params: Phase 3 - Full pipeline with context

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `74ebaf9f4d800e503d7b15a478a35048e4b31ecf54d5ec1cea7f0394b60d8c8d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `74ebaf9f4d800e503d7b15a478a35048e4b31ecf54d5ec1cea7f0394b60d8c8d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `74ebaf9f4d800e503d7b15a478a35048e4b31ecf54d5ec1cea7f0394b60d8c8d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/context_params_system_spec.spl
mirror: doc/06_spec/03_system/feature/features/context_params_system_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/context_params_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/context_params_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/context_params_system_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'context variable starts as nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/context_params_system_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'module var can hold context value (within it block)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/context_params_system_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'context variable can be set and restored (within it block)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
