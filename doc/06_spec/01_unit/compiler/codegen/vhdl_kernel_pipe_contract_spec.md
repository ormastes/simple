# Vhdl Kernel Pipe Contract Specification

> Tests covering VhdlPipeSpec validation, emit_vhdl_pipe_fifo, emit_vhdl_pipe_endpoints, emit_vhdl_pipe_topology.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Kernel Pipe Contract Specification

## Scenarios

### VhdlPipeSpec validation

#### (a) valid spec returns empty diagnostic

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- (a) valid spec returns empty diagnostic
   - Expected: diag equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(a) valid spec returns empty diagnostic")
val diag = vhdl_pipe_spec_validate(make_u32_pipe())
expect(diag).to_equal("")
```

</details>

#### (a) empty name is rejected

- (a) empty name is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(a) empty name is rejected")
val spec = make_pipe("", 32, 16)
val diag = vhdl_pipe_spec_validate(spec)
expect(diag).to_contain("VHDL-PIPE-INVALID")
expect(diag).to_contain("name")
```

</details>

#### (a) width = 0 is rejected

- (a) width = 0 is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(a) width = 0 is rejected")
val spec = make_pipe("p", 0, 16)
val diag = vhdl_pipe_spec_validate(spec)
expect(diag).to_contain("VHDL-PIPE-INVALID")
expect(diag).to_contain("element_width_bits")
```

</details>

#### (a) negative width is rejected

- (a) negative width is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(a) negative width is rejected")
val spec = make_pipe("p", -1, 16)
val diag = vhdl_pipe_spec_validate(spec)
expect(diag).to_contain("VHDL-PIPE-INVALID")
expect(diag).to_contain("element_width_bits")
```

</details>

#### (a) width > 512 is rejected

- (a) width > 512 is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(a) width > 512 is rejected")
val spec = make_pipe("p", 513, 16)
val diag = vhdl_pipe_spec_validate(spec)
expect(diag).to_contain("VHDL-PIPE-INVALID")
expect(diag).to_contain("element_width_bits")
```

</details>

#### (a) width = 512 is accepted

- (a) width = 512 is accepted
   - Expected: diag equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(a) width = 512 is accepted")
val diag = vhdl_pipe_spec_validate(make_wide_pipe())
expect(diag).to_equal("")
```

</details>

#### (a) depth = 0 is rejected

- (a) depth = 0 is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(a) depth = 0 is rejected")
val spec = make_pipe("p", 32, 0)
val diag = vhdl_pipe_spec_validate(spec)
expect(diag).to_contain("VHDL-PIPE-INVALID")
expect(diag).to_contain("depth")
```

</details>

#### (a) negative depth is rejected

- (a) negative depth is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(a) negative depth is rejected")
val spec = make_pipe("p", 32, -4)
val diag = vhdl_pipe_spec_validate(spec)
expect(diag).to_contain("VHDL-PIPE-INVALID")
expect(diag).to_contain("depth")
```

</details>

#### (a) depth = 1 is accepted (single-slot FIFO)

- (a) depth = 1 is accepted (single-slot FIFO)
   - Expected: diag equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(a) depth = 1 is accepted (single-slot FIFO)")
val diag = vhdl_pipe_spec_validate(make_pipe("p", 32, 1))
expect(diag).to_equal("")
```

</details>

### emit_vhdl_pipe_fifo

#### (b) returns Ok for valid spec

- (b) returns Ok for valid spec
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) returns Ok for valid spec")
val result = emit_vhdl_pipe_fifo(make_u32_pipe())
expect(result.is_ok()).to_equal(true)
```

</details>

#### (b) entity name is <pipe_name>_fifo

- (b) entity name is <pipe_name>_fifo


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) entity name is <pipe_name>_fifo")
val source = emit_vhdl_pipe_fifo(make_u32_pipe()).unwrap()
expect(source).to_contain("entity data_pipe_fifo is")
expect(source).to_contain("end entity data_pipe_fifo;")
```

</details>

#### (b) DEPTH generic constant is present

- (b) DEPTH generic constant is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) DEPTH generic constant is present")
val source = emit_vhdl_pipe_fifo(make_u32_pipe()).unwrap()
expect(source).to_contain("DEPTH")
expect(source).to_contain("16")
```

</details>

#### (b) standard control ports clk rst present

- (b) standard control ports clk rst present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) standard control ports clk rst present")
val source = emit_vhdl_pipe_fifo(make_u32_pipe()).unwrap()
expect(source).to_contain("clk : in bit")
expect(source).to_contain("rst : in bit")
```

</details>

#### (b) write-side handshake ports wr_en wr_data full present

- (b) write-side handshake ports wr_en wr_data full present


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) write-side handshake ports wr_en wr_data full present")
val source = emit_vhdl_pipe_fifo(make_u32_pipe()).unwrap()
expect(source).to_contain("wr_en")
expect(source).to_contain("wr_data")
expect(source).to_contain("full")
```

</details>

#### (b) read-side handshake ports rd_en rd_data empty present

- (b) read-side handshake ports rd_en rd_data empty present


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) read-side handshake ports rd_en rd_data empty present")
val source = emit_vhdl_pipe_fifo(make_u32_pipe()).unwrap()
expect(source).to_contain("rd_en")
expect(source).to_contain("rd_data")
expect(source).to_contain("empty")
```

</details>

#### (b) wr_data and rd_data use correct width for 32-bit pipe

- (b) wr_data and rd_data use correct width for 32-bit pipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) wr_data and rd_data use correct width for 32-bit pipe")
val source = emit_vhdl_pipe_fifo(make_u32_pipe()).unwrap()
expect(source).to_contain("31 downto 0")
```

</details>

#### (b) wr_data uses correct width for 512-bit pipe

- (b) wr_data uses correct width for 512-bit pipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) wr_data uses correct width for 512-bit pipe")
val source = emit_vhdl_pipe_fifo(make_wide_pipe()).unwrap()
expect(source).to_contain("511 downto 0")
```

</details>

#### (b) architecture rtl is emitted

- (b) architecture rtl is emitted


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) architecture rtl is emitted")
val source = emit_vhdl_pipe_fifo(make_u32_pipe()).unwrap()
expect(source).to_contain("architecture rtl of data_pipe_fifo is")
expect(source).to_contain("end architecture rtl;")
```

</details>

#### (b) circular buffer ram signal is declared

- (b) circular buffer ram signal is declared


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) circular buffer ram signal is declared")
val source = emit_vhdl_pipe_fifo(make_u32_pipe()).unwrap()
expect(source).to_contain("ram")
```

</details>

#### (b) write and read pointer signals present

- (b) write and read pointer signals present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) write and read pointer signals present")
val source = emit_vhdl_pipe_fifo(make_u32_pipe()).unwrap()
expect(source).to_contain("wr_ptr")
expect(source).to_contain("rd_ptr")
```

</details>

#### (b) rejects spec with empty name

- (b) rejects spec with empty name
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) rejects spec with empty name")
val result = emit_vhdl_pipe_fifo(make_pipe("", 32, 16))
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("VHDL-PIPE-INVALID")
```

</details>

#### (b) rejects spec with depth = 0

- (b) rejects spec with depth = 0
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) rejects spec with depth = 0")
val result = emit_vhdl_pipe_fifo(make_pipe("p", 32, 0))
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("VHDL-PIPE-INVALID")
```

</details>

#### (b) rejects spec with width = 0

- (b) rejects spec with width = 0
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) rejects spec with width = 0")
val result = emit_vhdl_pipe_fifo(make_pipe("p", 0, 8))
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("VHDL-PIPE-INVALID")
```

</details>

#### (b) rejects spec with width > 512

- (b) rejects spec with width > 512
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(b) rejects spec with width > 512")
val result = emit_vhdl_pipe_fifo(make_pipe("p", 513, 8))
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("VHDL-PIPE-INVALID")
```

</details>

### emit_vhdl_pipe_endpoints

#### (c) writer endpoint returns Ok

- (c) writer endpoint returns Ok
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(c) writer endpoint returns Ok")
val result = emit_vhdl_pipe_endpoints("producer_kernel", make_u32_pipe(), true)
expect(result.is_ok()).to_equal(true)
```

</details>

#### (c) reader endpoint returns Ok

- (c) reader endpoint returns Ok
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(c) reader endpoint returns Ok")
val result = emit_vhdl_pipe_endpoints("consumer_kernel", make_u32_pipe(), false)
expect(result.is_ok()).to_equal(true)
```

</details>

#### (c) writer block contains wr_en wr_data full ports

- (c) writer block contains wr_en wr_data full ports


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(c) writer block contains wr_en wr_data full ports")
val text_ = emit_vhdl_pipe_endpoints("prod", make_u32_pipe(), true).unwrap()
expect(text_).to_contain("data_pipe_wr_en")
expect(text_).to_contain("data_pipe_wr_data")
expect(text_).to_contain("data_pipe_full")
```

</details>

#### (c) reader block contains rd_en rd_data empty ports

- (c) reader block contains rd_en rd_data empty ports


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(c) reader block contains rd_en rd_data empty ports")
val text_ = emit_vhdl_pipe_endpoints("cons", make_u32_pipe(), false).unwrap()
expect(text_).to_contain("data_pipe_rd_en")
expect(text_).to_contain("data_pipe_rd_data")
expect(text_).to_contain("data_pipe_empty")
```

</details>

#### (c) writer block does not contain rd ports

- (c) writer block does not contain rd ports
   - Expected: text_ does not contain `rd_en`
   - Expected: text_ does not contain `rd_data`
   - Expected: text_ does not contain `empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(c) writer block does not contain rd ports")
val text_ = emit_vhdl_pipe_endpoints("prod", make_u32_pipe(), true).unwrap()
expect(text_.contains("rd_en")).to_equal(false)
expect(text_.contains("rd_data")).to_equal(false)
expect(text_.contains("empty")).to_equal(false)
```

</details>

#### (c) reader block does not contain wr ports

- (c) reader block does not contain wr ports
   - Expected: text_ does not contain `wr_en`
   - Expected: text_ does not contain `wr_data`
   - Expected: text_ does not contain `full`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(c) reader block does not contain wr ports")
val text_ = emit_vhdl_pipe_endpoints("cons", make_u32_pipe(), false).unwrap()
expect(text_.contains("wr_en")).to_equal(false)
expect(text_.contains("wr_data")).to_equal(false)
expect(text_.contains("full")).to_equal(false)
```

</details>

#### (c) writer block uses correct data width for 32-bit pipe

- (c) writer block uses correct data width for 32-bit pipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(c) writer block uses correct data width for 32-bit pipe")
val text_ = emit_vhdl_pipe_endpoints("prod", make_u32_pipe(), true).unwrap()
expect(text_).to_contain("31 downto 0")
```

</details>

#### (c) rejects empty kernel name

- (c) rejects empty kernel name
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(c) rejects empty kernel name")
val result = emit_vhdl_pipe_endpoints("", make_u32_pipe(), true)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("VHDL-PIPE-INVALID")
```

</details>

#### (c) rejects invalid spec (width = 0)

- (c) rejects invalid spec (width = 0)
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(c) rejects invalid spec (width = 0)")
val result = emit_vhdl_pipe_endpoints("kern", make_pipe("p", 0, 8), true)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("VHDL-PIPE-INVALID")
```

</details>

### emit_vhdl_pipe_topology

#### (d) returns Ok for valid inputs

- (d) returns Ok for valid inputs
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(d) returns Ok for valid inputs")
val result = emit_vhdl_pipe_topology("prod_kern", "cons_kern", make_u32_pipe())
expect(result.is_ok()).to_equal(true)
```

</details>

#### (d) wrapper entity is present in output

- (d) wrapper entity is present in output


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(d) wrapper entity is present in output")
val source = emit_vhdl_pipe_topology("prod_kern", "cons_kern", make_u32_pipe()).unwrap()
expect(source).to_contain("entity")
expect(source).to_contain("top")
```

</details>

#### (d) wrapper exposes clk and rst ports only

- (d) wrapper exposes clk and rst ports only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(d) wrapper exposes clk and rst ports only")
val source = emit_vhdl_pipe_topology("prod_kern", "cons_kern", make_u32_pipe()).unwrap()
expect(source).to_contain("clk : in bit")
expect(source).to_contain("rst : in bit")
```

</details>

#### (d) producer instance is present

- (d) producer instance is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(d) producer instance is present")
val source = emit_vhdl_pipe_topology("prod_kern", "cons_kern", make_u32_pipe()).unwrap()
expect(source).to_contain("producer_inst")
expect(source).to_contain("prod_kern")
```

</details>

#### (d) FIFO instance is present

- (d) FIFO instance is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(d) FIFO instance is present")
val source = emit_vhdl_pipe_topology("prod_kern", "cons_kern", make_u32_pipe()).unwrap()
expect(source).to_contain("fifo_inst")
expect(source).to_contain("data_pipe_fifo")
```

</details>

#### (d) consumer instance is present

- (d) consumer instance is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(d) consumer instance is present")
val source = emit_vhdl_pipe_topology("prod_kern", "cons_kern", make_u32_pipe()).unwrap()
expect(source).to_contain("consumer_inst")
expect(source).to_contain("cons_kern")
```

</details>

#### (d) pipe handshake signals are declared

- (d) pipe handshake signals are declared


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(d) pipe handshake signals are declared")
val source = emit_vhdl_pipe_topology("prod_kern", "cons_kern", make_u32_pipe()).unwrap()
expect(source).to_contain("data_pipe_wr_en")
expect(source).to_contain("data_pipe_wr_data")
expect(source).to_contain("data_pipe_full")
expect(source).to_contain("data_pipe_rd_en")
expect(source).to_contain("data_pipe_rd_data")
expect(source).to_contain("data_pipe_empty")
```

</details>

#### (d) architecture rtl is present

- (d) architecture rtl is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(d) architecture rtl is present")
val source = emit_vhdl_pipe_topology("prod_kern", "cons_kern", make_u32_pipe()).unwrap()
expect(source).to_contain("architecture rtl")
expect(source).to_contain("end architecture rtl;")
```

</details>

#### (d) rejects empty producer name

- (d) rejects empty producer name
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(d) rejects empty producer name")
val result = emit_vhdl_pipe_topology("", "cons_kern", make_u32_pipe())
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("VHDL-PIPE-INVALID")
expect(result.unwrap_err().message).to_contain("producer_entity_name")
```

</details>

#### (d) rejects empty consumer name

- (d) rejects empty consumer name
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(d) rejects empty consumer name")
val result = emit_vhdl_pipe_topology("prod_kern", "", make_u32_pipe())
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("VHDL-PIPE-INVALID")
expect(result.unwrap_err().message).to_contain("consumer_entity_name")
```

</details>

#### (d) rejects invalid spec

- (d) rejects invalid spec
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(d) rejects invalid spec")
val result = emit_vhdl_pipe_topology("prod_kern", "cons_kern", make_pipe("p", 0, 8))
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err().message).to_contain("VHDL-PIPE-INVALID")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/vhdl_kernel_pipe_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VhdlPipeSpec validation, emit_vhdl_pipe_fifo, emit_vhdl_pipe_endpoints, emit_vhdl_pipe_topology.
- VhdlPipeSpec validation
- emit_vhdl_pipe_fifo
- emit_vhdl_pipe_endpoints
- emit_vhdl_pipe_topology

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
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

- Canonical SPipe generation for source `a8f58f0b4b28b6aeb180990c2bf513a80ce1df58bce1a18f13b1502e7f926f71`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a8f58f0b4b28b6aeb180990c2bf513a80ce1df58bce1a18f13b1502e7f926f71`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a8f58f0b4b28b6aeb180990c2bf513a80ce1df58bce1a18f13b1502e7f926f71`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/vhdl_kernel_pipe_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/vhdl_kernel_pipe_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/vhdl_kernel_pipe_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/vhdl_kernel_pipe_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/vhdl_kernel_pipe_contract_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '(a) valid spec returns empty diagnostic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/vhdl_kernel_pipe_contract_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '(a) empty name is rejected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/vhdl_kernel_pipe_contract_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '(a) width = 0 is rejected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
