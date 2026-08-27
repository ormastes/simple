# Context Params Specification

> Tests covering desugar_context_params - basic context declaration, desugar_context_params - reference replacement, desugar_context_params - with_context transformation, desugar_context_params - tab-indented with_context body, desugar_context_params - multiple context variables, desugar_context_params - nested with_context counters.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context Params Specification

## Scenarios

### desugar_context_params - basic context declaration

#### transforms context val into module var

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- transforms context val into module var


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transforms context val into module var")
var src = "context val logger: Logger" + "\n"
src = src + "fn foo():" + "\n"
src = src + "    pass" + "\n"
val out = desugar_context_params(src)
expect(out).to_contain("var __ctx_logger: Logger = nil")
```

</details>

#### removes original context val declaration

- removes original context val declaration
   - Expected: has_context_val is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes original context val declaration")
var src = "context val logger: Logger" + "\n"
src = src + "fn foo(): pass" + "\n"
val out = desugar_context_params(src)
expect(out).to_contain("var __ctx_logger")
# The original line should be gone (replaced by var form)
val has_context_val = out.contains("context val logger")
expect(has_context_val).to_equal(false)
```

</details>

#### passes through source unchanged when no context declarations

- passes through source unchanged when no context declarations
   - Expected: out equals `src`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes through source unchanged when no context declarations")
val src = "fn foo() -> i64:" + "\n" + "    42" + "\n"
val out = desugar_context_params(src)
expect(out).to_equal(src)
```

</details>

### desugar_context_params - reference replacement

#### replaces context variable references with __ctx_ prefix

- replaces context variable references with __ctx_ prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces context variable references with __ctx_ prefix")
var src = "context val logger: Logger" + "\n"
src = src + "fn compile(source: text):" + "\n"
src = src + "    logger.log(source)" + "\n"
val out = desugar_context_params(src)
expect(out).to_contain("__ctx_logger.log(source)")
```

</details>

#### does not replace non-context variable names

- does not replace non-context variable names


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not replace non-context variable names")
var src = "context val logger: Logger" + "\n"
src = src + "fn foo(mylogger: Logger):" + "\n"
src = src + "    mylogger.log(x)" + "\n"
val out = desugar_context_params(src)
# mylogger should NOT be touched
expect(out).to_contain("mylogger.log(x)")
```

</details>

#### replaces context var at start of line

- replaces context var at start of line


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces context var at start of line")
var src = "context val config: Config" + "\n"
src = src + "fn setup():" + "\n"
src = src + "    config.init()" + "\n"
val out = desugar_context_params(src)
expect(out).to_contain("__ctx_config.init()")
```

</details>

#### does not replace a field access chain like obj.logger.log(x)

- does not replace a field access chain like obj.logger.log(x)
   - Expected: has_wrong is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not replace a field access chain like obj.logger.log(x)")
# `logger` here is a FIELD of `obj`, not the standalone context
# variable. Only a bare `logger.` reference should be rewritten.
var src = "context val logger: Logger" + "\n"
src = src + "fn foo(obj: Holder):" + "\n"
src = src + "    obj.logger.log(x)" + "\n"
val out = desugar_context_params(src)
expect(out).to_contain("obj.logger.log(x)")
val has_wrong = out.contains("obj.__ctx_logger.log(x)")
expect(has_wrong).to_equal(false)
```

</details>

### desugar_context_params - with_context transformation

#### replaces with_context with save/set/restore

- replaces with_context with save/set/restore


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces with_context with save/set/restore")
var src = "context val logger: Logger" + "\n"
src = src + "val x = 1" + "\n"
src = src + "with_context(logger: file_logger):" + "\n"
src = src + "    compile(source)" + "\n"
val out = desugar_context_params(src)
expect(out).to_contain("__saved_logger_0")
expect(out).to_contain("__ctx_logger = file_logger")
expect(out).to_contain("compile(source)")
```

</details>

#### saves old value before setting

- saves old value before setting
   - Expected: save_pos >= 0 is true
   - Expected: set_pos >= 0 is true
   - Expected: save_pos < set_pos is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("saves old value before setting")
var src = "context val logger: Logger" + "\n"
src = src + "with_context(logger: new_logger):" + "\n"
src = src + "    work()" + "\n"
val out = desugar_context_params(src)
# save must appear before set
val save_pos = _find_pos(out, "__saved_logger_0 = __ctx_logger")
val set_pos = _find_pos(out, "__ctx_logger = new_logger")
expect(save_pos >= 0).to_equal(true)
expect(set_pos >= 0).to_equal(true)
expect(save_pos < set_pos).to_equal(true)
```

</details>

#### restores old value after body

- restores old value after body
   - Expected: body_pos >= 0 is true
   - Expected: restore_pos >= 0 is true
   - Expected: body_pos < restore_pos is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restores old value after body")
var src = "context val logger: Logger" + "\n"
src = src + "with_context(logger: new_logger):" + "\n"
src = src + "    work()" + "\n"
val out = desugar_context_params(src)
# restore must appear after body
val body_pos = _find_pos(out, "work()")
val restore_pos = _find_pos(out, "__ctx_logger = __saved_logger_0")
expect(body_pos >= 0).to_equal(true)
expect(restore_pos >= 0).to_equal(true)
expect(body_pos < restore_pos).to_equal(true)
```

</details>

#### body lines are de-indented when emitted

- body lines are de-indented when emitted


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("body lines are de-indented when emitted")
var src = "context val logger: Logger" + "\n"
src = src + "with_context(logger: l):" + "\n"
src = src + "    do_work()" + "\n"
val out = desugar_context_params(src)
# do_work() should appear without extra indentation from with_context
expect(out).to_contain("do_work()")
```

</details>

### desugar_context_params - tab-indented with_context body

#### keeps a double-tab-indented body line inside the save/restore block

- keeps a double-tab-indented body line inside the save/restore block
   - Expected: body_pos >= 0 is true
   - Expected: restore_pos >= 0 is true
   - Expected: body_pos < restore_pos is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a double-tab-indented body line inside the save/restore block")
# Header is single-tab indented (real indent 4), body is double-tab
# indented (real indent 8). _get_indent must report 8 > 4 so the body
# line is recognised as part of the with_context block.
var src = "context val logger: Logger" + "\n"
src = src + "\twith_context(logger: l):" + "\n"
src = src + "\t\twork()" + "\n"
val out = desugar_context_params(src)
val body_pos = _find_pos(out, "work()")
val restore_pos = _find_pos(out, "__ctx_logger = __saved_logger_0")
expect(body_pos >= 0).to_equal(true)
expect(restore_pos >= 0).to_equal(true)
# The body call must run BEFORE the context is restored, not after.
expect(body_pos < restore_pos).to_equal(true)
```

</details>

### desugar_context_params - multiple context variables

#### declares multiple ctx vars

- declares multiple ctx vars


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares multiple ctx vars")
var src = "context val logger: Logger" + "\n"
src = src + "context val config: Config" + "\n"
src = src + "fn foo(): pass" + "\n"
val out = desugar_context_params(src)
expect(out).to_contain("var __ctx_logger: Logger = nil")
expect(out).to_contain("var __ctx_config: Config = nil")
```

</details>

#### replaces multiple context variable references

- replaces multiple context variable references


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces multiple context variable references")
var src = "context val logger: Logger" + "\n"
src = src + "context val config: Config" + "\n"
src = src + "fn setup():" + "\n"
src = src + "    logger.log(x)" + "\n"
src = src + "    config.init()" + "\n"
val out = desugar_context_params(src)
expect(out).to_contain("__ctx_logger.log(x)")
expect(out).to_contain("__ctx_config.init()")
```

</details>

#### with_context sets multiple vars

- with_context sets multiple vars


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with_context sets multiple vars")
var src = "context val logger: Logger" + "\n"
src = src + "context val config: Config" + "\n"
src = src + "with_context(logger: l, config: c):" + "\n"
src = src + "    run()" + "\n"
val out = desugar_context_params(src)
expect(out).to_contain("__ctx_logger = l")
expect(out).to_contain("__ctx_config = c")
expect(out).to_contain("run()")
```

</details>

### desugar_context_params - nested with_context counters

#### uses distinct save var names for nested blocks

- uses distinct save var names for nested blocks
   - Expected: has_0 is true
   - Expected: has_1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses distinct save var names for nested blocks")
var src = "context val logger: Logger" + "\n"
src = src + "with_context(logger: l1):" + "\n"
src = src + "    with_context(logger: l2):" + "\n"
src = src + "        work()" + "\n"
val out = desugar_context_params(src)
# Both blocks need unique counter suffixes
val has_0 = out.contains("__saved_logger_0")
val has_1 = out.contains("__saved_logger_1")
expect(has_0).to_equal(true)
expect(has_1).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/desugar/context_params_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering desugar_context_params - basic context declaration, desugar_context_params - reference replacement, desugar_context_params - with_context transformation, desugar_context_params - tab-indented with_context body, desugar_context_params - multiple context variables, desugar_context_params - nested with_context counters.
- desugar_context_params - basic context declaration
- desugar_context_params - reference replacement
- desugar_context_params - with_context transformation
- desugar_context_params - tab-indented with_context body
- desugar_context_params - multiple context variables
- desugar_context_params - nested with_context counters

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `d7907d97f24c430f1a66078d005d98b781047675efc55f4cb56a1e6117465f6f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d7907d97f24c430f1a66078d005d98b781047675efc55f4cb56a1e6117465f6f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d7907d97f24c430f1a66078d005d98b781047675efc55f4cb56a1e6117465f6f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/desugar/context_params_spec.spl
mirror: doc/06_spec/unit/app/desugar/context_params_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/desugar/context_params_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/desugar/context_params_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/desugar/context_params_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'transforms context val into module var' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/context_params_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes original context val declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/context_params_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes through source unchanged when no context declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
