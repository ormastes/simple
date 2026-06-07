# VHDL Subprogram Emission

> VHDL Subprogram Emission Specification

<!-- sdn-diagram:id=vhdl_subprogram_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_subprogram_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_subprogram_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_subprogram_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VHDL Subprogram Emission

VHDL Subprogram Emission Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #vhdl-subprogram-emission, VHDL-PARITY-010 |
| Category | Backend / VHDL |
| Difficulty | 3/5 |
| Status | Active |
| Source | `test/01_unit/compiler/vhdl/vhdl_subprogram_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

VHDL Subprogram Emission Specification

Tests VHDL function/procedure emission in VhdlBuilder and verifies
subprogram helper definitions in vhdl_helpers.spl via text-grep.

## Scenarios

### VHDL Subprogram Emission - functions

#### emits a parameterless function

1. var builder = VhdlBuilder create
2. builder emit function begin
3. builder emit function body begin
4. builder emit function return
5. builder emit function end
6. check
7. check
8. check
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = VhdlBuilder create
2. ["a : std logic vector
3. "std logic vector
4. builder emit function body begin
5. builder emit function return
6. builder emit function end
7. check
8. check
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = VhdlBuilder create
2. ["a : signed
3. "signed
4. builder emit function body begin
5. builder emit function return
6. builder emit function end
7. check
8. check
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = VhdlBuilder create
2. builder emit process var
3. builder emit function body begin
4. builder emit if begin
5. builder emit var assign
6. builder emit elsif
7. builder emit var assign
8. builder emit else
9. builder emit var assign
10. builder emit if end
11. builder emit function return
12. builder emit function end
13. check
14. check
15. check
16. check
17. check
18. check
19. check
20. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = VhdlBuilder create
2. builder emit library header
3. builder emit entity begin
4. builder emit port begin
5. builder emit port
6. builder emit port end
7. builder emit entity end
8. builder emit architecture begin
9. builder emit function begin
10. builder emit function body begin
11. builder emit function return
12. builder emit function end
13. builder emit architecture body begin
14. builder emit comment
15. builder emit architecture end
16. check
17. check
18. check
19. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = VhdlBuilder create
2. builder emit procedure begin
3. builder emit procedure body begin
4. builder emit comment
5. builder emit procedure end
6. check
7. check
8. check
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = VhdlBuilder create
2. "x : in signed
3. "hi : out signed
4. "lo : out signed
5. builder emit procedure body begin
6. builder emit var assign
7. builder emit var assign
8. builder emit procedure end
9. check
10. check
11. check
12. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = VhdlBuilder create
2. builder emit procedure body begin
3. builder emit var assign
4. builder emit procedure end
5. check
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = VhdlBuilder create
2. builder emit architecture begin
3. builder emit process var
4. builder emit procedure body begin
5. builder emit var assign
6. builder emit var assign
7. builder emit var assign
8. builder emit procedure end
9. builder emit architecture body begin
10. builder emit architecture end
11. check
12. check
13. check
14. check
15. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl") ?? ""
check(source.len() > 0)
check(source.contains("fn vhdl_helper_is_subprogram_eligible"))
check(source.contains("has_vhdl_metadata"))
check(source.contains("is_hardware"))
check(source.contains("has_clocked"))
```

</details>

#### defines vhdl_subprogram_name with simple_fn_ prefix

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl") ?? ""
check(source.contains("fn vhdl_subprogram_name"))
check(source.contains("simple_fn_"))
check(source.contains("vhdl_sanitize_identifier"))
```

</details>

#### defines vhdl_subprogram_name_plan returning VhdlHelperNamePlan

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl") ?? ""
check(source.contains("fn vhdl_subprogram_name_plan"))
check(source.contains("VhdlHelperNamePlan"))
```

</details>

#### defines collision detection with reserved word checks

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl") ?? ""
check(source.contains("fn vhdl_check_name_collisions"))
check(source.contains("fn vhdl_is_reserved_word"))
check(source.contains("collides with a VHDL reserved word"))
```

</details>

#### defines vhdl_helper_collision_message for diagnostics

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl") ?? ""
check(source.contains("fn vhdl_helper_collision_message"))
check(source.contains("Duplicate VHDL helper subprogram name"))
```

</details>

#### defines vhdl_helper_is_procedure check

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl") ?? ""
check(source.contains("fn vhdl_helper_is_procedure"))
check(source.contains("MirTypeKind.Unit"))
```

</details>

### VHDL Subprogram Emission - builder source verification

#### defines function emission methods

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_builder.spl") ?? ""
check(source.len() > 0)
check(source.contains("me emit_function_begin"))
check(source.contains("me emit_function_body_begin"))
check(source.contains("me emit_function_return"))
check(source.contains("me emit_function_end"))
```

</details>

#### defines procedure emission methods

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_builder.spl") ?? ""
check(source.contains("me emit_procedure_begin"))
check(source.contains("me emit_procedure_body_begin"))
check(source.contains("me emit_procedure_end"))
```

</details>

#### function begin emits correct VHDL template

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_builder.spl") ?? ""
# Verify the emit_function_begin method uses correct VHDL template
check(source.contains(r"function {name}("))
check(source.contains(r"return {return_type} is"))
```

</details>

#### procedure begin emits correct VHDL template

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/70.backend/backend/vhdl/vhdl_builder.spl") ?? ""
# Verify the emit_procedure_begin method uses correct VHDL template
check(source.contains(r"procedure {name}("))
check(source.contains(r"end procedure {name};"))
```

</details>

### VHDL Subprogram Emission - identifier sanitization

#### sanitizer replaces unsafe characters

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check
3. check
4. check
5. check
6. check
7. check
8. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
