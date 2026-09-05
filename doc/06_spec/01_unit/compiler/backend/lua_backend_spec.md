# Lua Backend Specification

> Tests covering Lua backend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lua Backend Specification

## Scenarios

### Lua backend

#### emits module header local M

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits module header local M


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits module header local M")
var t = MirToLua.create("mymod")
val src = t.translate_module(build_const_module())
expect(src).to_contain("local M = {}")
```

</details>

#### emits return M at end

- emits return M at end


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits return M at end")
var t = MirToLua.create("mymod")
val src = t.translate_module(build_const_module())
expect(src).to_contain("return M")
```

</details>

#### emits function declaration with correct name

- emits function declaration with correct name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits function declaration with correct name")
var t = MirToLua.create("mymod")
val src = t.translate_module(build_const_module())
expect(src).to_contain("function M.const42(")
```

</details>

#### emits end after function body

- emits end after function body


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits end after function body")
var t = MirToLua.create("mymod")
val src = t.translate_module(build_const_module())
expect(src).to_contain("end")
```

</details>

#### emits integer constant assignment

- emits integer constant assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits integer constant assignment")
var t = MirToLua.create("mymod")
val src = t.translate_module(build_const_module())
expect(src).to_contain("= 42")
```

</details>

#### emits return statement

- emits return statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits return statement")
var t = MirToLua.create("mymod")
val src = t.translate_module(build_const_module())
expect(src).to_contain("return ")
```

</details>

#### emits block label syntax

- emits block label syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits block label syntax")
var t = MirToLua.create("mymod")
val src = t.translate_module(build_const_module())
expect(src).to_contain("::bb")
```

</details>

#### emits add function declaration

- emits add function declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits add function declaration")
var t = MirToLua.create("mymod")
val src = t.translate_module(build_add_module())
expect(src).to_contain("function M.add(")
```

</details>

#### emits addition operator

- emits addition operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits addition operator")
var t = MirToLua.create("mymod")
val src = t.translate_module(build_add_module())
expect(src).to_contain(" + ")
```

</details>

#### quoted strings escape double-quotes

- quoted strings escape double-quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quoted strings escape double-quotes")
var t = MirToLua.create("test")
val q = t.lua_quoted("say \"hello\"")
expect(q).to_contain("\\\"")
```

</details>

#### binop ne emits lua not-equal operator

- binop ne emits lua not-equal operator
   - Expected: op equals `~=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binop ne emits lua not-equal operator")
var t = MirToLua.create("test")
val op = t.binop_text(MirBinOp.Ne)
expect(op).to_equal("~=")
```

</details>

#### binop add emits plus

- binop add emits plus
   - Expected: op equals `+`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binop add emits plus")
var t = MirToLua.create("test")
val op = t.binop_text(MirBinOp.Add)
expect(op).to_equal("+")
```

</details>

#### const_value_text for bool true

- const_value_text for bool true
   - Expected: v equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("const_value_text for bool true")
var t = MirToLua.create("test")
val v = t.const_value_text(MirConstValue.Bool(true))
expect(v).to_equal("true")
```

</details>

#### const_value_text for bool false

- const_value_text for bool false
   - Expected: v equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("const_value_text for bool false")
var t = MirToLua.create("test")
val v = t.const_value_text(MirConstValue.Bool(false))
expect(v).to_equal("false")
```

</details>

#### const_value_text for integer

- const_value_text for integer
   - Expected: v equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("const_value_text for integer")
var t = MirToLua.create("test")
val v = t.const_value_text(MirConstValue.Int(99))
expect(v).to_equal("99")
```

</details>

#### const_value_text for string

- const_value_text for string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("const_value_text for string")
var t = MirToLua.create("test")
val v = t.const_value_text(MirConstValue.Str("hello"))
expect(v).to_contain("hello")
```

</details>

#### emits generation comment header

- emits generation comment header


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits generation comment header")
var t = MirToLua.create("mymod")
val src = t.translate_module(build_const_module())
expect(src).to_contain("-- Generated by Simple Lua backend")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/lua_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lua backend.
- Lua backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `abde889ff0d998aa9c60f074cda2e48490cd2769682c22aa153c077a46395498`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `abde889ff0d998aa9c60f074cda2e48490cd2769682c22aa153c077a46395498`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `abde889ff0d998aa9c60f074cda2e48490cd2769682c22aa153c077a46395498`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/lua_backend_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/lua_backend_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/lua_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/lua_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/lua_backend_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits module header local M' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/lua_backend_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits return M at end' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/lua_backend_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits function declaration with correct name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
