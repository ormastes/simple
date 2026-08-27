# VHDL Subprogram Emission

> Verifies that VhdlBuilder emits correct VHDL function and procedure blocks, and that the helpers module provides subprogram eligibility, naming, and collision detection utilities.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VHDL Subprogram Emission

Verifies that VhdlBuilder emits correct VHDL function and procedure blocks, and that the helpers module provides subprogram eligibility, naming, and collision detection utilities.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/vhdl/vhdl_subprogram_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that VhdlBuilder emits correct VHDL function and procedure
blocks, and that the helpers module provides subprogram eligibility,
naming, and collision detection utilities.

## Syntax

- `emit_function_begin(name, params, return_type)` emits a VHDL function header
- `emit_procedure_begin(name, params)` emits a VHDL procedure header
- Helper functions: `vhdl_subprogram_name`, `vhdl_helper_is_subprogram_eligible`

## Key Concepts

- Pure combinational helpers lower to VHDL functions
- Multi-output helpers lower to VHDL procedures with out parameters
- @hardware / @clocked helpers remain entities (not subprograms)
- Subprogram names use `simple_fn_` prefix for collision safety

## Behavior

- Function declarations include typed parameter list and return type
- Procedure declarations include directional parameter list
- Names are sanitized and prefixed to avoid VHDL reserved word collisions

## Related Specifications

- `test/unit/compiler/backend/vhdl_builder_spec.spl`
- `test/unit/compiler/backend/vhdl_backend_spec.spl`

## Implementation Notes

Text-grep based — reads source files and checks generated VHDL text.
Does not depend on full compilation pipeline.

## Scenarios

### VHDL Subprogram Emission - functions

#### emits a parameterless function

- emits a parameterless function


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a parameterless function")
var builder = VhdlBuilder.create("test_mod")
builder.emit_function_begin("simple_fn_get_zero", [], "integer")
builder.emit_function_body_begin()
builder.emit_function_return("0")
builder.emit_function_end("simple_fn_get_zero")

val vhdl = builder.build()

check(vhdl.contains("function simple_fn_get_zero return integer is"))
check(vhdl.contains("begin"))
check(vhdl.contains("return 0;"))
check(vhdl.contains("end function simple_fn_get_zero;"))
```

</details>

#### emits a single-parameter function

- emits a single-parameter function


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a single-parameter function")
var builder = VhdlBuilder.create("test_mod")
builder.emit_function_begin(
    "simple_fn_invert",
    ["a : std_logic_vector(7 downto 0)"],
    "std_logic_vector(7 downto 0)"
)
builder.emit_function_body_begin()
builder.emit_function_return("not a")
builder.emit_function_end("simple_fn_invert")

val vhdl = builder.build()

check(vhdl.contains("function simple_fn_invert(a : std_logic_vector(7 downto 0)) return std_logic_vector(7 downto 0) is"))
check(vhdl.contains("return not a;"))
check(vhdl.contains("end function simple_fn_invert;"))
```

</details>

#### emits a multi-parameter function

- emits a multi-parameter function


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a multi-parameter function")
var builder = VhdlBuilder.create("test_mod")
builder.emit_function_begin(
    "simple_fn_test_add",
    ["a : signed(31 downto 0)", "b : signed(31 downto 0)"],
    "signed(31 downto 0)"
)
builder.emit_function_body_begin()
builder.emit_function_return("a + b")
builder.emit_function_end("simple_fn_test_add")

val vhdl = builder.build()

check(vhdl.contains("function simple_fn_test_add(a : signed(31 downto 0); b : signed(31 downto 0)) return signed(31 downto 0) is"))
check(vhdl.contains("return a + b;"))
check(vhdl.contains("end function simple_fn_test_add;"))
```

</details>

#### emits a function with local variables

- emits a function with local variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a function with local variables")
var builder = VhdlBuilder.create("test_mod")
builder.emit_function_begin(
    "simple_fn_clamp",
    ["x : integer", "lo : integer", "hi : integer"],
    "integer"
)
builder.emit_process_var("result", "integer", nil)
builder.emit_function_body_begin()
builder.emit_if_begin("x < lo")
builder.emit_var_assign("result", "lo")
builder.emit_elsif("x > hi")
builder.emit_var_assign("result", "hi")
builder.emit_else()
builder.emit_var_assign("result", "x")
builder.emit_if_end()
builder.emit_function_return("result")
builder.emit_function_end("simple_fn_clamp")

val vhdl = builder.build()

check(vhdl.contains("function simple_fn_clamp(x : integer; lo : integer; hi : integer) return integer is"))
check(vhdl.contains("variable result : integer;"))
check(vhdl.contains("if x < lo then"))
check(vhdl.contains("result := lo;"))
check(vhdl.contains("elsif x > hi then"))
check(vhdl.contains("result := hi;"))
check(vhdl.contains("return result;"))
check(vhdl.contains("end function simple_fn_clamp;"))
```

</details>

#### places function in architecture declarative region

- places function in architecture declarative region


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("places function in architecture declarative region")
var builder = VhdlBuilder.create("arch_test")
builder.emit_library_header()
builder.emit_entity_begin("top")
builder.emit_port_begin()
builder.emit_port("clk", "in", "std_logic", true)
builder.emit_port_end()
builder.emit_entity_end("top")
builder.emit_architecture_begin("top", "rtl")
# Function goes in declarative region (before begin)
builder.emit_function_begin("simple_fn_helper", ["x : integer"], "integer")
builder.emit_function_body_begin()
builder.emit_function_return("x + 1")
builder.emit_function_end("simple_fn_helper")
builder.emit_architecture_body_begin()
builder.emit_comment("architecture body uses the function")
builder.emit_architecture_end("rtl")

val vhdl = builder.build()

check(vhdl.contains("architecture rtl of top is"))
check(vhdl.contains("function simple_fn_helper(x : integer) return integer is"))
check(vhdl.contains("end function simple_fn_helper;"))
check(vhdl.contains("end architecture rtl;"))
```

</details>

### VHDL Subprogram Emission - procedures

#### emits a parameterless procedure

- emits a parameterless procedure


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a parameterless procedure")
var builder = VhdlBuilder.create("test_mod")
builder.emit_procedure_begin("simple_fn_noop", [])
builder.emit_procedure_body_begin()
builder.emit_comment("no-op")
builder.emit_procedure_end("simple_fn_noop")

val vhdl = builder.build()

check(vhdl.contains("procedure simple_fn_noop is"))
check(vhdl.contains("begin"))
check(vhdl.contains("-- no-op"))
check(vhdl.contains("end procedure simple_fn_noop;"))
```

</details>

#### emits a procedure with out parameters

- emits a procedure with out parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a procedure with out parameters")
var builder = VhdlBuilder.create("test_mod")
builder.emit_procedure_begin(
    "simple_fn_split",
    [
        "x : in signed(31 downto 0)",
        "hi : out signed(15 downto 0)",
        "lo : out signed(15 downto 0)"
    ]
)
builder.emit_procedure_body_begin()
builder.emit_var_assign("hi", "x(31 downto 16)")
builder.emit_var_assign("lo", "x(15 downto 0)")
builder.emit_procedure_end("simple_fn_split")

val vhdl = builder.build()

check(vhdl.contains("procedure simple_fn_split(x : in signed(31 downto 0); hi : out signed(15 downto 0); lo : out signed(15 downto 0)) is"))
check(vhdl.contains("hi := x(31 downto 16);"))
check(vhdl.contains("lo := x(15 downto 0);"))
check(vhdl.contains("end procedure simple_fn_split;"))
```

</details>

#### emits a procedure with inout parameter

- emits a procedure with inout parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a procedure with inout parameter")
var builder = VhdlBuilder.create("test_mod")
builder.emit_procedure_begin(
    "simple_fn_increment",
    ["counter : inout integer"]
)
builder.emit_procedure_body_begin()
builder.emit_var_assign("counter", "counter + 1")
builder.emit_procedure_end("simple_fn_increment")

val vhdl = builder.build()

check(vhdl.contains("procedure simple_fn_increment(counter : inout integer) is"))
check(vhdl.contains("counter := counter + 1;"))
check(vhdl.contains("end procedure simple_fn_increment;"))
```

</details>

#### places procedure in architecture declarative region

- places procedure in architecture declarative region


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("places procedure in architecture declarative region")
var builder = VhdlBuilder.create("arch_test")
builder.emit_architecture_begin("top", "rtl")
builder.emit_procedure_begin(
    "simple_fn_swap",
    ["a : inout integer", "b : inout integer"]
)
builder.emit_process_var("tmp", "integer", nil)
builder.emit_procedure_body_begin()
builder.emit_var_assign("tmp", "a")
builder.emit_var_assign("a", "b")
builder.emit_var_assign("b", "tmp")
builder.emit_procedure_end("simple_fn_swap")
builder.emit_architecture_body_begin()
builder.emit_architecture_end("rtl")

val vhdl = builder.build()

check(vhdl.contains("architecture rtl of top is"))
check(vhdl.contains("procedure simple_fn_swap(a : inout integer; b : inout integer) is"))
check(vhdl.contains("variable tmp : integer;"))
check(vhdl.contains("end procedure simple_fn_swap;"))
check(vhdl.contains("end architecture rtl;"))
```

</details>

### VHDL Subprogram Emission - helpers source verification

#### defines vhdl_helper_is_subprogram_eligible function

- defines vhdl_helper_is_subprogram_eligible function


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines vhdl_helper_is_subprogram_eligible function")
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl") ?? ""
check(source.len() > 0)
check(source.contains("fn vhdl_helper_is_subprogram_eligible"))
check(source.contains("has_vhdl_metadata"))
check(source.contains("is_hardware"))
check(source.contains("has_clocked"))
```

</details>

#### defines vhdl_subprogram_name with simple_fn_ prefix

- defines vhdl_subprogram_name with simple_fn_ prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines vhdl_subprogram_name with simple_fn_ prefix")
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl") ?? ""
check(source.contains("fn vhdl_subprogram_name"))
check(source.contains("simple_fn_"))
check(source.contains("vhdl_sanitize_identifier"))
```

</details>

#### defines vhdl_subprogram_name_plan returning VhdlHelperNamePlan

- defines vhdl_subprogram_name_plan returning VhdlHelperNamePlan


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines vhdl_subprogram_name_plan returning VhdlHelperNamePlan")
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl") ?? ""
check(source.contains("fn vhdl_subprogram_name_plan"))
check(source.contains("VhdlHelperNamePlan"))
```

</details>

#### defines collision detection with reserved word checks

- defines collision detection with reserved word checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines collision detection with reserved word checks")
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl") ?? ""
check(source.contains("fn vhdl_check_name_collisions"))
check(source.contains("fn vhdl_is_reserved_word"))
check(source.contains("collides with a VHDL reserved word"))
```

</details>

#### defines vhdl_helper_collision_message for diagnostics

- defines vhdl_helper_collision_message for diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines vhdl_helper_collision_message for diagnostics")
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl") ?? ""
check(source.contains("fn vhdl_helper_collision_message"))
check(source.contains("Duplicate VHDL helper subprogram name"))
```

</details>

#### defines vhdl_helper_is_procedure check

- defines vhdl_helper_is_procedure check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines vhdl_helper_is_procedure check")
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl") ?? ""
check(source.contains("fn vhdl_helper_is_procedure"))
check(source.contains("MirTypeKind.Unit"))
```

</details>

### VHDL Subprogram Emission - builder source verification

#### defines function emission methods

- defines function emission methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines function emission methods")
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_builder.spl") ?? ""
check(source.len() > 0)
check(source.contains("me emit_function_begin"))
check(source.contains("me emit_function_body_begin"))
check(source.contains("me emit_function_return"))
check(source.contains("me emit_function_end"))
```

</details>

#### defines procedure emission methods

- defines procedure emission methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines procedure emission methods")
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_builder.spl") ?? ""
check(source.contains("me emit_procedure_begin"))
check(source.contains("me emit_procedure_body_begin"))
check(source.contains("me emit_procedure_end"))
```

</details>

#### function begin emits correct VHDL template

- function begin emits correct VHDL template


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function begin emits correct VHDL template")
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_builder.spl") ?? ""
# Verify the emit_function_begin method uses correct VHDL template
check(source.contains(r"function {name}("))
check(source.contains(r"return {return_type} is"))
```

</details>

#### procedure begin emits correct VHDL template

- procedure begin emits correct VHDL template


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("procedure begin emits correct VHDL template")
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_builder.spl") ?? ""
# Verify the emit_procedure_begin method uses correct VHDL template
check(source.contains(r"procedure {name}("))
check(source.contains(r"end procedure {name};"))
```

</details>

### VHDL Subprogram Emission - identifier sanitization

#### sanitizer replaces unsafe characters

- sanitizer replaces unsafe characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sanitizer replaces unsafe characters")
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl") ?? ""
check(source.contains("fn vhdl_sanitize_identifier"))
# Must replace common unsafe chars
check(source.contains(".replace(\" \", \"_\")"))
check(source.contains(".replace(\"-\", \"_\")"))
check(source.contains(".replace(\".\", \"_\")"))
check(source.contains(".replace(\":\", \"_\")"))
```

</details>

#### covers VHDL-2008 reserved words

- covers VHDL-2008 reserved words


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers VHDL-2008 reserved words")
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl") ?? ""
check(source.contains("fn vhdl_is_reserved_word"))
# Spot-check critical reserved words
check(source.contains("\"signal\""))
check(source.contains("\"process\""))
check(source.contains("\"entity\""))
check(source.contains("\"architecture\""))
check(source.contains("\"function\""))
check(source.contains("\"procedure\""))
check(source.contains("\"variable\""))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `5d20440a8f3a4a94adc793af46093e02d31f93cab0095abce1e38f6ee7a9efff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d20440a8f3a4a94adc793af46093e02d31f93cab0095abce1e38f6ee7a9efff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d20440a8f3a4a94adc793af46093e02d31f93cab0095abce1e38f6ee7a9efff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/vhdl/vhdl_subprogram_spec.spl
mirror: doc/06_spec/01_unit/compiler/vhdl/vhdl_subprogram_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/vhdl/vhdl_subprogram_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/vhdl/vhdl_subprogram_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/vhdl/vhdl_subprogram_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a parameterless function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/vhdl/vhdl_subprogram_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a single-parameter function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/vhdl/vhdl_subprogram_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a multi-parameter function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
