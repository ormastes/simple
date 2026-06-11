# vhdl_backend_spec

> VHDL Backend Integration Specification

<!-- sdn-diagram:id=vhdl_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_backend_spec -> compiler
vhdl_backend_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 58 | 58 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vhdl_backend_spec

VHDL Backend Integration Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #vhdl-backend |
| Category | Backend |
| Difficulty | 3/5 |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vhdl_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

VHDL Backend Integration Specification

Tests VhdlBackend compilation pipeline via VhdlBuilder integration.
Verifies that generated VHDL is structurally valid for common patterns.

## Scenarios

### VHDL Backend - registration

#### preserves named clock domain metadata in MIR domain helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val domain = vhdl_clock_domain_from_metadata(VhdlClockedMetadata(
    clock_signal: "clk_core",
    reset_signal: "rst_n",
    has_reset: true,
    reset_polarity: VhdlResetPolarity.ActiveLow,
    reset_synchrony: VhdlResetSynchrony.Sync,
    domain: "core-domain",
    is_valid: true,
    validation_errors: []
))

expect(domain.name).to_equal("core-domain")
expect(domain.clock_signal).to_equal("clk_core")
expect(domain.reset_signal.unwrap()).to_equal("rst_n")
expect(domain.reset_polarity).to_equal(VhdlResetPolarity.ActiveLow)
expect(domain.reset_synchrony).to_equal(VhdlResetSynchrony.Sync)
```

</details>

#### resolves vhdl by backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = backend_for_name("vhdl")
expect(kind.?).to_equal(true)
expect(kind.unwrap()).to_equal(BackendKind.Vhdl)
```

</details>

#### lists VHDL as an available backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backends = available_backends()
var found = false
for backend in backends:
    if backend == BackendKind.Vhdl:
        found = true
expect(found).to_equal(true)
```

</details>

### VHDL Backend - simple function compilation

#### generates entity with input/output ports for add function

1. var builder = VhdlBuilder create
2. builder emit library header
3. builder emit entity begin
4. builder emit port begin
5. builder emit port
6. builder emit port
7. builder emit port
8. builder emit port end
9. builder emit entity end
10. builder emit architecture begin
11. builder emit architecture body begin
12. builder emit signal assign
13. builder emit architecture end
14. check
15. check
16. check
17. check
18. check
19. check
20. check
21. check
22. check
23. check
24. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = VhdlBuilder.create("add")
builder.emit_library_header()
builder.emit_entity_begin("add")
builder.emit_port_begin()
builder.emit_port("a", "in", "signed(31 downto 0)", false)
builder.emit_port("b", "in", "signed(31 downto 0)", false)
builder.emit_port("result_out", "out", "signed(31 downto 0)", true)
builder.emit_port_end()
builder.emit_entity_end("add")
builder.emit_architecture_begin("add", "rtl")
builder.emit_architecture_body_begin()
builder.emit_signal_assign("result_out", "a + b")
builder.emit_architecture_end("rtl")
val vhdl = builder.build()

# Verify structural VHDL validity
check(vhdl.contains("library ieee;"))
check(vhdl.contains("use ieee.std_logic_1164.all;"))
check(vhdl.contains("use ieee.numeric_std.all;"))
check(vhdl.contains("entity add is"))
check(vhdl.contains("a : in signed(31 downto 0);"))
check(vhdl.contains("b : in signed(31 downto 0);"))
check(vhdl.contains("result_out : out signed(31 downto 0)"))
check(vhdl.contains("end entity add;"))
check(vhdl.contains("architecture rtl of add is"))
check(vhdl.contains("result_out <= a + b;"))
check(vhdl.contains("end architecture rtl;"))
```

</details>

### VHDL Backend - type declaration package

#### generates package with record and enum types

1. var builder = VhdlBuilder create
2. builder emit library header
3. builder emit package begin
4. builder emit type decl
5. builder emit type decl
6. builder emit constant decl
7. builder emit package end
8. check
9. check
10. check
11. check
12. check
13. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()
var builder = VhdlBuilder.create("types_mod")
builder.emit_library_header()
builder.emit_package_begin("types_mod")

# Enum type
val enum_def = mapper.map_enum_type(["Idle", "Running", "Done"])
builder.emit_type_decl("state_t", enum_def)

# Record type
val record_def = mapper.map_record([("x", "signed(31 downto 0)"), ("y", "signed(31 downto 0)")])
builder.emit_type_decl("point_t", record_def)

# Constant
builder.emit_constant_decl("MAX_COUNT", "integer", "255")
builder.emit_package_end("types_mod")
val vhdl = builder.build()

check(vhdl.contains("package types_mod_pkg is"))
check(vhdl.contains("type state_t is (Idle, Running, Done);"))
check(vhdl.contains("type point_t is record"))
check(vhdl.contains("x : signed(31 downto 0);"))
check(vhdl.contains("constant MAX_COUNT : integer := 255;"))
check(vhdl.contains("end package types_mod_pkg;"))
```

</details>

### VHDL Backend - signal assignments

#### generates arithmetic signal assignments

1. var builder = VhdlBuilder create
2. builder emit architecture begin
3. builder emit signal decl
4. builder emit signal decl
5. builder emit architecture body begin
6. builder emit signal assign
7. builder emit signal assign
8. builder emit architecture end
9. check
10. check
11. check
12. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = VhdlBuilder.create("arith")
builder.emit_architecture_begin("arith", "rtl")
builder.emit_signal_decl("sum", "signed(31 downto 0)", nil)
builder.emit_signal_decl("diff", "signed(31 downto 0)", nil)
builder.emit_architecture_body_begin()
builder.emit_signal_assign("sum", "a + b")
builder.emit_signal_assign("diff", "a - b")
builder.emit_architecture_end("rtl")
val vhdl = builder.build()

check(vhdl.contains("signal sum : signed(31 downto 0);"))
check(vhdl.contains("signal diff : signed(31 downto 0);"))
check(vhdl.contains("sum <= a + b;"))
check(vhdl.contains("diff <= a - b;"))
```

</details>

#### generates bitwise signal assignments

1. var builder = VhdlBuilder create
2. builder emit architecture begin
3. builder emit architecture body begin
4. builder emit signal assign
5. builder emit signal assign
6. builder emit signal assign
7. builder emit architecture end
8. check
9. check
10. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = VhdlBuilder.create("bitwise")
builder.emit_architecture_begin("bitwise", "rtl")
builder.emit_architecture_body_begin()
builder.emit_signal_assign("result", "a and b")
builder.emit_signal_assign("result2", "a or b")
builder.emit_signal_assign("result3", "a xor b")
builder.emit_architecture_end("rtl")
val vhdl = builder.build()

check(vhdl.contains("result <= a and b;"))
check(vhdl.contains("result2 <= a or b;"))
check(vhdl.contains("result3 <= a xor b;"))
```

</details>

### VHDL Backend - type mapper integration

#### maps all integer types for port declarations

1. var builder = VhdlBuilder create
2. builder emit entity begin
3. builder emit port begin
4. builder emit port
5. builder emit port
6. builder emit port
7. builder emit port
8. builder emit port
9. builder emit port
10. builder emit port end
11. builder emit entity end
12. check
13. check
14. check
15. check
16. check
17. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()
var builder = VhdlBuilder.create("typed")
builder.emit_entity_begin("typed")
builder.emit_port_begin()
builder.emit_port("a8", "in", mapper.map_primitive(PrimitiveType.I8), false)
builder.emit_port("a16", "in", mapper.map_primitive(PrimitiveType.I16), false)
builder.emit_port("a32", "in", mapper.map_primitive(PrimitiveType.I32), false)
builder.emit_port("a64", "in", mapper.map_primitive(PrimitiveType.I64), false)
builder.emit_port("u8", "in", mapper.map_primitive(PrimitiveType.U8), false)
builder.emit_port("flag", "in", mapper.map_primitive(PrimitiveType.Bool), true)
builder.emit_port_end()
builder.emit_entity_end("typed")
val vhdl = builder.build()

check(vhdl.contains("a8 : in signed(7 downto 0);"))
check(vhdl.contains("a16 : in signed(15 downto 0);"))
check(vhdl.contains("a32 : in signed(31 downto 0);"))
check(vhdl.contains("a64 : in signed(63 downto 0);"))
check(vhdl.contains("u8 : in unsigned(7 downto 0);"))
check(vhdl.contains("flag : in bit"))
```

</details>

#### maps resolved types for std_logic ports

1. var builder = VhdlBuilder create
2. builder emit entity begin
3. builder emit port begin
4. builder emit port
5. builder emit port
6. builder emit port end
7. builder emit entity end
8. check
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create_resolved()
var builder = VhdlBuilder.create("resolved")
builder.emit_entity_begin("resolved")
builder.emit_port_begin()
builder.emit_port("clk", "in", mapper.map_primitive(PrimitiveType.Bool), false)
builder.emit_port("data", "in", mapper.bit_vector_type(8), true)
builder.emit_port_end()
builder.emit_entity_end("resolved")
val vhdl = builder.build()

check(vhdl.contains("clk : in std_logic;"))
check(vhdl.contains("data : in std_logic_vector(7 downto 0)"))
```

</details>

### VHDL Backend - complete module compilation

#### generates complete ALU module with package

1. var pkg = VhdlBuilder create
2. pkg emit library header
3. pkg emit package begin
4. pkg emit type decl
5. pkg emit constant decl
6. pkg emit package end
7. var ent = VhdlBuilder create
8. ent emit library header
9. ent emit use package
10. ent emit entity begin
11. ent emit port begin
12. ent emit port
13. ent emit port
14. ent emit port
15. ent emit port
16. ent emit port end
17. ent emit entity end
18. ent emit architecture begin
19. ent emit architecture body begin
20. ent emit process begin
21. ent emit process body begin
22. ent emit comment
23. ent emit signal assign
24. ent emit process end
25. ent emit architecture end
26. check
27. check
28. check
29. check
30. check
31. check
32. check
33. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()

# Package
var pkg = VhdlBuilder.create("alu")
pkg.emit_library_header()
pkg.emit_package_begin("alu")
val op_enum = mapper.map_enum_type(["OpAdd", "OpSub", "OpAnd", "OpOr"])
pkg.emit_type_decl("alu_op_t", op_enum)
pkg.emit_constant_decl("WIDTH", "integer", "32")
pkg.emit_package_end("alu")

# Entity
var ent = VhdlBuilder.create("alu")
ent.emit_library_header()
ent.emit_use_package("work", "alu_pkg")
ent.emit_entity_begin("alu")
ent.emit_port_begin()
ent.emit_port("op", "in", "alu_op_t", false)
ent.emit_port("a", "in", "signed(31 downto 0)", false)
ent.emit_port("b", "in", "signed(31 downto 0)", false)
ent.emit_port("result_out", "out", "signed(31 downto 0)", true)
ent.emit_port_end()
ent.emit_entity_end("alu")
ent.emit_architecture_begin("alu", "rtl")
ent.emit_architecture_body_begin()
ent.emit_process_begin(Some("alu_proc"), ["op", "a", "b"])
ent.emit_process_body_begin()
ent.emit_comment("ALU operation selection")
ent.emit_signal_assign("result_out", "a + b")
ent.emit_process_end(Some("alu_proc"))
ent.emit_architecture_end("rtl")

val pkg_vhdl = pkg.build()
val ent_vhdl = ent.build()

# Verify package
check(pkg_vhdl.contains("package alu_pkg is"))
check(pkg_vhdl.contains("type alu_op_t is (OpAdd, OpSub, OpAnd, OpOr);"))
check(pkg_vhdl.contains("constant WIDTH : integer := 32;"))

# Verify entity
check(ent_vhdl.contains("use work.alu_pkg.all;"))
check(ent_vhdl.contains("entity alu is"))
check(ent_vhdl.contains("alu_proc: process(op, a, b)"))
check(ent_vhdl.contains("end process alu_proc;"))
check(ent_vhdl.contains("end architecture rtl;"))
```

</details>

### VHDL Backend - real backend compilation

#### compiles MIR locals to ports and result output

1. check
2. check
3. check
4. check
5. check
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_simple_backend()
val result = backend.compile(single_block_module("adder_mod", make_adder_function()))
check(result.is_ok())
val compiled = result.unwrap()

check(compiled.vhdl.contains("a : in signed(31 downto 0);"))
check(compiled.vhdl.contains("b : in signed(31 downto 0);"))
check(compiled.vhdl.contains("result_out : out signed(31 downto 0)"))
check(compiled.vhdl.contains("signal sum_sig : signed(31 downto 0);"))
check(compiled.vhdl.contains("sum_sig <= a + b;"))
check(compiled.vhdl.contains("result_out <= sum_sig;"))
```

</details>

#### matches checked backend-generated adder golden

1. check
   - Expected: generated equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_simple_backend()
val result = backend.compile(single_block_module("adder_mod", make_adder_function()))
check(result.is_ok())
val generated = normalize_vhdl(result.unwrap().vhdl)
val expected = normalize_vhdl(rt_file_read_text("examples/09_embedded/vhdl/backend/golden/adder.vhd") ?? "")
expect(generated).to_equal(expected)
```

</details>

#### declares fixed local arrays through constrained memory type templates

1. id: BlockId
2. label: Some
3. kind: MirInstKind Const
4. kind: MirInstKind Copy
5. terminator: MirTerminator Return
6. symbol: SymbolId
7. signature: MirSignature
8. entry block: BlockId entry
9. span: empty span
10. check
11. check
12. check
13. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_local = make_return_local(1, make_i32())
val scratch_local = make_temp_local(2, "scratch", make_u8_array(8))
val answer_local = make_temp_local(3, "answer", make_i32())
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.Const(LocalId(id: 3), MirConstValue.Int(1), make_i32()),
            span: nil
        ),
        MirInst(
            kind: MirInstKind.Copy(LocalId(id: 1), LocalId(id: 3)),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 130),
    name: "fixed_local_memory",
    signature: MirSignature(params: [], return_type: make_i32(), is_variadic: false),
    locals: [ret_local, scratch_local, answer_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)

val result = make_simple_backend().compile(single_block_module("fixed_memory_mod", func))
check(result.is_ok())
val vhdl = result.unwrap().vhdl
check(vhdl.contains("type scratch_memory_t is array (0 to 7) of unsigned(7 downto 0);"))
check(vhdl.contains("signal scratch : scratch_memory_t;"))
check(not vhdl.contains("signal scratch : array (0 to 7)"))
```

</details>

#### rejects array ports before emitting anonymous array VHDL

1. id: BlockId
2. label: Some
3. terminator: MirTerminator Return
4. symbol: SymbolId
5. signature: MirSignature
6. entry block: BlockId entry
7. span: empty span
8. check
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg_local = make_arg_local(1, 0, "data", make_u8_array(4))
val ret_local = make_return_local(2, make_i32())
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 131),
    name: "array_port",
    signature: MirSignature(params: [make_u8_array(4)], return_type: make_i32(), is_variadic: false),
    locals: [arg_local, ret_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)

val result = make_simple_backend().compile(single_block_module("array_port_mod", func))
check(result.is_err())
check(result.unwrap_err().message.contains("VHDL-MEM-GENERAL"))
```

</details>

#### compiles package declarations through the backend trait path

1. symbol: SymbolId
2. MirFieldDef
3. MirFieldDef
4. symbol: SymbolId
5. type : make i32
6. value: MirConstValue Int
7. check
8. check
9. check
10. check
11. check
12. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val point_type = MirTypeDef(
    symbol: SymbolId(id: 20),
    name: "point_t",
    kind: MirTypeDefKind.Struct([
        MirFieldDef(name: "x", type_: make_i32(), offset: 0, has_bits_attr: false, bits_width: 0),
        MirFieldDef(name: "valid", type_: make_bool(), offset: 4, has_bits_attr: false, bits_width: 0)
    ]),
    is_export_c: false,
    export_name: ""
)
val max_constant = MirConstant(
    symbol: SymbolId(id: 21),
    name: "MAX_VALUE",
    type_: make_i32(),
    value: MirConstValue.Int(7)
)
var types: Dict<SymbolId, MirTypeDef> = {}
types[point_type.symbol] = point_type
var constants: Dict<SymbolId, MirConstant> = {}
constants[max_constant.symbol] = max_constant
val module = MirModule(name: "pkg_demo", functions: {}, statics: {}, constants: constants, types: types)

val backend = make_simple_backend()
val pkg_result = backend.compile_package(module)
check(pkg_result.is_ok())
val pkg_vhdl = pkg_result.unwrap()

check(pkg_vhdl.contains("package pkg_demo_pkg is"))
check(pkg_vhdl.contains("type point_t is record"))
check(pkg_vhdl.contains("x : signed(31 downto 0);"))
check(pkg_vhdl.contains("valid : bit;"))
check(pkg_vhdl.contains("constant MAX_VALUE : signed(31 downto 0) := to_signed(7, 32);"))
```

</details>

#### compiles tuple aggregates through a generated tuple record type

1. id: BlockId
2. label: Some
3. LocalId
4. MirOperand
5. MirOperand
6. kind: MirInstKind Copy
7. terminator: MirTerminator Return
8. symbol: SymbolId
9. signature: MirSignature
10. entry block: BlockId entry
11. span: empty span
12. check
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

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tuple_type = make_tuple_i32_bool()
val src_local = make_arg_local(1, 0, "a", make_i32())
val flag_local = make_arg_local(2, 1, "flag", make_bool())
val ret_local = make_return_local(3, tuple_type)
val tuple_local = make_temp_local(4, "tuple_sig", tuple_type)
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.Aggregate(
                LocalId(id: 4),
                AggregateKind.Tuple,
                [
                    MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
                    MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2)))
                ]
            ),
            span: nil
        ),
        MirInst(
            kind: MirInstKind.Copy(LocalId(id: 3), LocalId(id: 4)),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 41),
    name: "tuple_pack",
    signature: MirSignature(params: [make_i32(), make_bool()], return_type: tuple_type, is_variadic: false),
    locals: [src_local, flag_local, ret_local, tuple_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
val backend = make_simple_backend()
val result = backend.compile(single_block_module("tuple_mod", func))
check(result.is_ok())
val compiled = result.unwrap()
check(compiled.package_vhdl.?)
val tuple_pkg = compiled.package_vhdl.unwrap()
check(tuple_pkg.contains("type tuple_t_0 is record"))
check(tuple_pkg.contains("f0 : signed(31 downto 0);"))
check(tuple_pkg.contains("f1 : bit;"))
check(compiled.vhdl.contains("result_out : out tuple_t_0"))
check(compiled.vhdl.contains("signal tuple_sig : tuple_t_0;"))
check(compiled.vhdl.contains("tuple_sig <= (f0 => a, f1 => flag);"))
check(compiled.vhdl.contains("result_out <= tuple_sig;"))
```

</details>

#### rejects anonymous hardware tuple outputs before VHDL emission

1.   make adder function
2. symbol: SymbolId
3. signature: MirSignature
4. vhdl metadata: make hardware meta
5. check
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = MirFunction(
    ..make_adder_function(),
    symbol: SymbolId(id: 42),
    name: "anonymous_hardware_outputs",
    signature: MirSignature(params: [], return_type: make_tuple_i32_bool(), is_variadic: false),
    has_vhdl_metadata: true,
    vhdl_metadata: make_hardware_meta()
)
val result = make_simple_backend().compile(single_block_module("anonymous_hardware_output_mod", func))
check(result.is_err())
check(result.unwrap_err().message.contains("Anonymous VHDL hardware tuple outputs require labels"))
check(result.unwrap_err().message.contains("(name: type, ...)"))
```

</details>

#### compiles payloadless enum aggregates to variant literals

1. SymbolId
2. id: BlockId
3. label: Some
4. LocalId
5. AggregateKind Enum
6. kind: MirInstKind Copy
7. terminator: MirTerminator Return
8. symbol: SymbolId
9. signature: MirSignature
10. entry block: BlockId entry
11. span: empty span
12. check
13. check
14. check
15. check
16. check
17. check
18. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 60 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state_type = make_payloadless_enum_type_def(
    SymbolId(id: 55),
    "state_t",
    ["Idle-State", "Running.Fast", "Done"]
)
var types: Dict<SymbolId, MirTypeDef> = {}
types[state_type.symbol] = state_type
val ret_local = make_return_local(1, MirType(kind: MirTypeKind.Enum(state_type.symbol)))
val state_local = make_temp_local(2, "state_sig", MirType(kind: MirTypeKind.Enum(state_type.symbol)))
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.Aggregate(
                LocalId(id: 2),
                AggregateKind.Enum(state_type.symbol, 1),
                []
            ),
            span: nil
        ),
        MirInst(
            kind: MirInstKind.Copy(LocalId(id: 1), LocalId(id: 2)),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 56),
    name: "state_pack",
    signature: MirSignature(params: [], return_type: MirType(kind: MirTypeKind.Enum(state_type.symbol)), is_variadic: false),
    locals: [ret_local, state_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
var functions: Dict<SymbolId, MirFunction> = {}
functions[func.symbol] = func
val module = MirModule(name: "enum_mod", functions: functions, statics: {}, constants: {}, types: types)
val backend = make_simple_backend()
val result = backend.compile(module)
check(result.is_ok())
val compiled = result.unwrap()
check(compiled.package_vhdl.?)
val enum_pkg = compiled.package_vhdl.unwrap()
check(enum_pkg.contains("type state_t is (Idle_State, Running_Fast, Done);"))
check(compiled.vhdl.contains("result_out : out state_t"))
check(compiled.vhdl.contains("signal state_sig : state_t;"))
check(compiled.vhdl.contains("state_sig <= Running_Fast;"))
check(compiled.vhdl.contains("result_out <= state_sig;"))
```

</details>

#### compiles process enum aggregates to sanitized variant literals

1. SymbolId
2. id: BlockId
3. label: Some
4. LocalId
5. AggregateKind Enum
6. terminator: MirTerminator Return
7. id: BlockId
8. label: Some
9. VhdlProcessKind Combinational
10. BlockId
11. terminator: MirTerminator Return
12. symbol: SymbolId
13. signature: MirSignature
14. entry block: BlockId entry
15. span: empty span
16. check
17. check
18. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 64 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state_type = make_payloadless_enum_type_def(
    SymbolId(id: 59),
    "process_state_t",
    ["Needs-Reset", "Ready.State"]
)
var types: Dict<SymbolId, MirTypeDef> = {}
types[state_type.symbol] = state_type
val ret_local = make_return_local(1, MirType(kind: MirTypeKind.Enum(state_type.symbol)))
val body_block = MirBlock(
    id: BlockId(id: 1),
    label: Some("proc_body"),
    instructions: [
        MirInst(
            kind: MirInstKind.Aggregate(
                LocalId(id: 1),
                AggregateKind.Enum(state_type.symbol, 0),
                []
            ),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val entry_block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.VhdlProcess(
                VhdlProcessKind.Combinational([]),
                BlockId(id: 1)
            ),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 60),
    name: "process_state_pack",
    signature: MirSignature(params: [], return_type: MirType(kind: MirTypeKind.Enum(state_type.symbol)), is_variadic: false),
    locals: [ret_local],
    blocks: [entry_block, body_block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
var functions: Dict<SymbolId, MirFunction> = {}
functions[func.symbol] = func
val module = MirModule(name: "process_enum_mod", functions: functions, statics: {}, constants: {}, types: types)
val backend = make_simple_backend()
val result = backend.compile(module)
check(result.is_ok())
val compiled = result.unwrap()
check(compiled.package_vhdl.unwrap().contains("type process_state_t is (Needs_Reset, Ready_State);"))
check(compiled.vhdl.contains("result_out <= Needs_Reset;"))
```

</details>

#### emits payload enum package records with tag and payload fields

1. MirVariantDef
2. MirVariantDef
3. check
4. check
5. check
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload_symbol = SymbolId(id: 57)
val payload_enum = MirTypeDef(
    symbol: payload_symbol,
    name: "maybe_t",
    kind: MirTypeDefKind.Enum([
        MirVariantDef(name: "None", discriminant: 0, payload: nil),
        MirVariantDef(name: "Some", discriminant: 1, payload: Some(make_i32()))
    ]),
    is_export_c: false,
    export_name: ""
)
var types: Dict<SymbolId, MirTypeDef> = {}
types[payload_symbol] = payload_enum
val module = MirModule(name: "payload_enum_mod", functions: {}, statics: {}, constants: {}, types: types)
val backend = make_simple_backend()
val result = backend.compile(module)
check(result.is_ok())
val compiled = result.unwrap()
val package_vhdl = compiled.package_vhdl.unwrap()
check(package_vhdl.contains("type maybe_t_tag_t is (None, Some);"))
check(package_vhdl.contains("type maybe_t is record"))
check(package_vhdl.contains("tag : maybe_t_tag_t;"))
check(package_vhdl.contains("Some_payload : signed(31 downto 0);"))
```

</details>

#### lowers payload-free variants of payload enums with default payload fields

1. MirVariantDef
2. MirVariantDef
3. id: BlockId
4. label: Some
5. LocalId
6. AggregateKind Enum
7. span: Some
8. kind: MirInstKind Copy
9. terminator: MirTerminator Return
10. symbol: SymbolId
11. signature: MirSignature
12. entry block: BlockId entry
13. span: empty span
14. var backend = make simple backend
15. backend active type defs = backend active type defs set
16. check
17. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload_symbol = SymbolId(id: 61)
val payload_enum = MirTypeDef(
    symbol: payload_symbol,
    name: "maybe_agg_t",
    kind: MirTypeDefKind.Enum([
        MirVariantDef(name: "None", discriminant: 0, payload: nil),
        MirVariantDef(name: "Some", discriminant: 1, payload: Some(make_i32()))
    ]),
    is_export_c: false,
    export_name: ""
)
val enum_type = MirType(kind: MirTypeKind.Enum(payload_symbol))
val ret_local = make_return_local(1, enum_type)
val state_local = make_temp_local(2, "state_sig", enum_type)
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.Aggregate(
                LocalId(id: 2),
                AggregateKind.Enum(payload_symbol, 0),
                []
            ),
            span: Some(Span(start: 40, end: 45, line: 7, col: 9, file: "", length: 0))
        ),
        MirInst(
            kind: MirInstKind.Copy(LocalId(id: 1), LocalId(id: 2)),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 62),
    name: "payload_state_pack",
    signature: MirSignature(params: [], return_type: enum_type, is_variadic: false),
    locals: [ret_local, state_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
var backend = make_simple_backend()
backend.active_type_defs = backend.active_type_defs.set(payload_symbol.id, payload_enum)
val result = backend.compile_function(VhdlBuilder.create("payload_agg_mod"), func)
check(result.is_ok())
val compiled = result.unwrap()
check(compiled.vhdl.contains("state_sig <= (tag => None, Some_payload => to_signed(0, 32));"))
```

</details>

#### lowers payload variants of payload enums with the payload operand

1. MirVariantDef
2. MirVariantDef
3. id: BlockId
4. label: Some
5. LocalId
6. AggregateKind Enum
7. [MirOperand
8. MirInst
9. terminator: MirTerminator Return
10. symbol: SymbolId
11. signature: MirSignature
12. entry block: BlockId entry
13. span: empty span
14. var backend = make simple backend
15. backend active type defs = backend active type defs set
16. check
17. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload_symbol = SymbolId(id: 65)
val payload_enum = MirTypeDef(
    symbol: payload_symbol,
    name: "maybe_some_t",
    kind: MirTypeDefKind.Enum([
        MirVariantDef(name: "None", discriminant: 0, payload: nil),
        MirVariantDef(name: "Some", discriminant: 1, payload: Some(make_i32()))
    ]),
    is_export_c: false,
    export_name: ""
)
val enum_type = MirType(kind: MirTypeKind.Enum(payload_symbol))
val ret_local = make_return_local(1, enum_type)
val state_local = make_temp_local(2, "state_sig", enum_type)
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.Aggregate(
                LocalId(id: 2),
                AggregateKind.Enum(payload_symbol, 1),
                [MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(7), make_i32()))]
            ),
            span: nil
        ),
        MirInst(kind: MirInstKind.Copy(LocalId(id: 1), LocalId(id: 2)), span: nil)
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 66),
    name: "payload_some_pack",
    signature: MirSignature(params: [], return_type: enum_type, is_variadic: false),
    locals: [ret_local, state_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
var backend = make_simple_backend()
backend.active_type_defs = backend.active_type_defs.set(payload_symbol.id, payload_enum)
val result = backend.compile_function(VhdlBuilder.create("payload_some_mod"), func)
check(result.is_ok())
val compiled = result.unwrap()
check(compiled.vhdl.contains("state_sig <= (tag => Some, Some_payload => to_signed(7, 32));"))
```

</details>

#### projects payload enum tag and payload fields from tagged records

1. MirVariantDef
2. MirVariantDef
3. id: BlockId
4. label: Some
5. LocalId
6. AggregateKind Enum
7. [MirOperand
8. LocalId
9. MirOperand
10. MirInst
11. terminator: MirTerminator Return
12. symbol: SymbolId
13. signature: MirSignature
14. entry block: BlockId entry
15. span: empty span
16. var backend = make simple backend
17. backend active type defs = backend active type defs set
18. check
19. check
20. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 64 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload_symbol = SymbolId(id: 165)
val payload_enum = MirTypeDef(
    symbol: payload_symbol,
    name: "maybe_project_t",
    kind: MirTypeDefKind.Enum([
        MirVariantDef(name: "None", discriminant: 0, payload: nil),
        MirVariantDef(name: "Some", discriminant: 1, payload: Some(make_i32()))
    ]),
    is_export_c: false,
    export_name: ""
)
val enum_type = MirType(kind: MirTypeKind.Enum(payload_symbol))
val ret_local = make_return_local(1, make_i32())
val state_local = make_temp_local(2, "state_sig", enum_type)
val payload_local = make_temp_local(3, "payload_sig", make_i32())
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.Aggregate(
                LocalId(id: 2),
                AggregateKind.Enum(payload_symbol, 1),
                [MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(9), make_i32()))]
            ),
            span: nil
        ),
        MirInst(
            kind: MirInstKind.GetField(
                LocalId(id: 3),
                MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2))),
                1
            ),
            span: nil
        ),
        MirInst(kind: MirInstKind.Copy(LocalId(id: 1), LocalId(id: 3)), span: nil)
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 166),
    name: "payload_project",
    signature: MirSignature(params: [], return_type: make_i32(), is_variadic: false),
    locals: [ret_local, state_local, payload_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
var backend = make_simple_backend()
backend.active_type_defs = backend.active_type_defs.set(payload_symbol.id, payload_enum)
val result = backend.compile_function(VhdlBuilder.create("payload_project_mod"), func)
check(result.is_ok())
val compiled = result.unwrap()
check(compiled.vhdl.contains("payload_sig <= state_sig.Some_payload;"))
check(compiled.vhdl.contains("result_out <= payload_sig;"))
```

</details>

#### switches on payload enum tags while projecting payload fields

1. MirVariantDef
2. MirVariantDef
3. id: BlockId
4. label: Some
5. MirOperand
6. [SwitchCase
7. BlockId
8. id: BlockId
9. label: Some
10. LocalId
11. MirOperand
12. terminator: MirTerminator Return
13. id: BlockId
14. label: Some
15. terminator: MirTerminator Return
16. symbol: SymbolId
17. signature: MirSignature
18. entry block: BlockId entry
19. span: empty span
20. var backend = make simple backend
21. backend active type defs = backend active type defs set
22. check
23. check
24. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 71 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload_symbol = SymbolId(id: 167)
val payload_enum = MirTypeDef(
    symbol: payload_symbol,
    name: "maybe_match_t",
    kind: MirTypeDefKind.Enum([
        MirVariantDef(name: "None", discriminant: 0, payload: nil),
        MirVariantDef(name: "Some", discriminant: 1, payload: Some(make_i32()))
    ]),
    is_export_c: false,
    export_name: ""
)
val enum_type = MirType(kind: MirTypeKind.Enum(payload_symbol))
val arg_local = make_arg_local(1, 0, "state", enum_type)
val ret_local = make_return_local(2, make_i32())
val payload_local = make_temp_local(3, "payload_sig", make_i32())
val entry_block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [],
    terminator: MirTerminator.Switch(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
        [SwitchCase(value: 1, target: BlockId(id: 1))],
        BlockId(id: 2)
    )
)
val some_block = MirBlock(
    id: BlockId(id: 1),
    label: Some("some"),
    instructions: [
        MirInst(
            kind: MirInstKind.GetField(
                LocalId(id: 3),
                MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
                1
            ),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 3)))))
)
val none_block = MirBlock(
    id: BlockId(id: 2),
    label: Some("none"),
    instructions: [],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(0), make_i32()))))
)
val func = MirFunction(
    symbol: SymbolId(id: 168),
    name: "payload_match",
    signature: MirSignature(params: [enum_type], return_type: make_i32(), is_variadic: false),
    locals: [arg_local, ret_local, payload_local],
    blocks: [entry_block, some_block, none_block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
var backend = make_simple_backend()
backend.active_type_defs = backend.active_type_defs.set(payload_symbol.id, payload_enum)
val result = backend.compile_function(VhdlBuilder.create("payload_match_mod"), func)
check(result.is_ok())
val compiled = result.unwrap()
check(compiled.vhdl.contains("payload_sig <= state.Some_payload;"))
check(compiled.vhdl.contains("state.tag = Some"))
```

</details>

#### lowers unit-return hardware entities without result ports

1. id: BlockId
2. label: Some
3. terminator: MirTerminator Return
4. symbol: SymbolId
5. signature: MirSignature
6. locals: [make return local
7. entry block: BlockId entry
8. span: empty span
9. check
10. check
11. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 169),
    name: "unit_sink",
    signature: MirSignature(params: [], return_type: make_unit(), is_variadic: false),
    locals: [make_return_local(1, make_unit())],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
val result = make_simple_backend().compile_function(VhdlBuilder.create("unit_sink_mod"), func)
check(result.is_ok())
val compiled = result.unwrap()
check(compiled.vhdl.contains("entity unit_sink is"))
check(compiled.vhdl.contains("port ("))
check(compiled.vhdl.contains("result_out")).to_equal(false)
```

</details>

#### switches on payload enum tags inside combinational processes

1. MirVariantDef
2. MirVariantDef
3. id: BlockId
4. label: Some
5. VhdlProcessKind Combinational
6. BlockId
7. terminator: MirTerminator Return
8. id: BlockId
9. label: Some
10. MirOperand
11. [SwitchCase
12. BlockId
13. id: BlockId
14. label: Some
15. LocalId
16. MirOperand
17. MirInst
18. terminator: MirTerminator Return
19. id: BlockId
20. label: Some
21. LocalId
22. MirOperand
23. terminator: MirTerminator Return
24. symbol: SymbolId
25. signature: MirSignature
26. entry block: BlockId entry
27. span: empty span
28. var backend = make simple backend
29. backend active type defs = backend active type defs set
30. check
31. check
32. check
33. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 95 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload_symbol = SymbolId(id: 170)
val payload_enum = MirTypeDef(
    symbol: payload_symbol,
    name: "maybe_proc_match_t",
    kind: MirTypeDefKind.Enum([
        MirVariantDef(name: "None", discriminant: 0, payload: nil),
        MirVariantDef(name: "Some", discriminant: 1, payload: Some(make_i32()))
    ]),
    is_export_c: false,
    export_name: ""
)
val enum_type = MirType(kind: MirTypeKind.Enum(payload_symbol))
val arg_local = make_arg_local(1, 0, "state", enum_type)
val ret_local = make_return_local(2, make_i32())
val payload_local = make_temp_local(3, "payload_sig", make_i32())
val entry_block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.VhdlProcess(
                VhdlProcessKind.Combinational(["state"]),
                BlockId(id: 1)
            ),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val body_block = MirBlock(
    id: BlockId(id: 1),
    label: Some("body"),
    instructions: [],
    terminator: MirTerminator.Switch(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
        [SwitchCase(value: 1, target: BlockId(id: 2))],
        BlockId(id: 3)
    )
)
val some_block = MirBlock(
    id: BlockId(id: 2),
    label: Some("some"),
    instructions: [
        MirInst(
            kind: MirInstKind.GetField(
                LocalId(id: 3),
                MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
                1
            ),
            span: nil
        ),
        MirInst(kind: MirInstKind.Copy(LocalId(id: 2), LocalId(id: 3)), span: nil)
    ],
    terminator: MirTerminator.Return(nil)
)
val none_block = MirBlock(
    id: BlockId(id: 3),
    label: Some("none"),
    instructions: [
        MirInst(
            kind: MirInstKind.Copy(
                LocalId(id: 2),
                MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(0), make_i32()))
            ),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 171),
    name: "payload_proc_match",
    signature: MirSignature(params: [enum_type], return_type: make_i32(), is_variadic: false),
    locals: [arg_local, ret_local, payload_local],
    blocks: [entry_block, body_block, some_block, none_block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
var backend = make_simple_backend()
backend.active_type_defs = backend.active_type_defs.set(payload_symbol.id, payload_enum)
val result = backend.compile_function(VhdlBuilder.create("payload_proc_match_mod"), func)
check(result.is_ok())
val compiled = result.unwrap()
check(compiled.vhdl.contains("process(state)"))
check(compiled.vhdl.contains("if state.tag = Some then"))
check(compiled.vhdl.contains("payload_sig <= state.Some_payload;"))
```

</details>

#### lowers payload-free variants of payload enums inside processes

1. MirVariantDef
2. MirVariantDef
3. id: BlockId
4. label: Some
5. LocalId
6. AggregateKind Enum
7. span: Some
8. terminator: MirTerminator Return
9. id: BlockId
10. label: Some
11. kind: MirInstKind VhdlProcess
12. terminator: MirTerminator Return
13. symbol: SymbolId
14. signature: MirSignature
15. entry block: BlockId entry
16. span: empty span
17. var backend = make simple backend
18. backend active type defs = backend active type defs set
19. check
20. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 63 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload_symbol = SymbolId(id: 63)
val payload_enum = MirTypeDef(
    symbol: payload_symbol,
    name: "maybe_proc_t",
    kind: MirTypeDefKind.Enum([
        MirVariantDef(name: "None", discriminant: 0, payload: nil),
        MirVariantDef(name: "Some", discriminant: 1, payload: Some(make_i32()))
    ]),
    is_export_c: false,
    export_name: ""
)
val enum_type = MirType(kind: MirTypeKind.Enum(payload_symbol))
val ret_local = make_return_local(1, enum_type)
val body_block = MirBlock(
    id: BlockId(id: 1),
    label: Some("body"),
    instructions: [
        MirInst(
            kind: MirInstKind.Aggregate(
                LocalId(id: 1),
                AggregateKind.Enum(payload_symbol, 0),
                []
            ),
            span: Some(Span(start: 80, end: 86, line: 12, col: 5, file: "", length: 0))
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val entry_block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.VhdlProcess(VhdlProcessKind.Combinational([]), BlockId(id: 1)),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 64),
    name: "payload_process_state_pack",
    signature: MirSignature(params: [], return_type: enum_type, is_variadic: false),
    locals: [ret_local],
    blocks: [entry_block, body_block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
var backend = make_simple_backend()
backend.active_type_defs = backend.active_type_defs.set(payload_symbol.id, payload_enum)
val result = backend.compile_function(VhdlBuilder.create("payload_proc_mod"), func)
check(result.is_ok())
val compiled = result.unwrap()
check(compiled.vhdl.contains("result_out <= (tag => None, Some_payload => to_signed(0, 32));"))
```

</details>

#### rejects enum literal VHDL name collisions after sanitization

1. MirVariantDef
2. MirVariantDef
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enum_symbol = SymbolId(id: 58)
val bad_enum = MirTypeDef(
    symbol: enum_symbol,
    name: "bad_enum_t",
    kind: MirTypeDefKind.Enum([
        MirVariantDef(name: "Needs-Reset", discriminant: 0, payload: nil),
        MirVariantDef(name: "Needs_Reset", discriminant: 1, payload: nil)
    ]),
    is_export_c: false,
    export_name: ""
)
var types: Dict<SymbolId, MirTypeDef> = {}
types[enum_symbol] = bad_enum
val module = MirModule(name: "bad_enum_mod", functions: {}, statics: {}, constants: {}, types: types)
val backend = make_simple_backend()
val result = backend.compile(module)
check(result.is_err())
check(result.unwrap_err().message.contains("Duplicate VHDL enum literal after sanitization"))
```

</details>

#### rejects floating-point input ports before VHDL emission with a source span

1. id: BlockId
2. label: Some
3. terminator: MirTerminator Return
4. symbol: SymbolId
5. signature: MirSignature
6. entry block: BlockId entry
7. span: diagnostic span
8. check
9. check
10. check
11. check
   - Expected: err.location equals `7:3-8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg_local = make_arg_local(1, 0, "f_in", make_f32())
val ret_local = make_return_local(2, make_i32())
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 70),
    name: "float_port",
    signature: MirSignature(params: [make_f32()], return_type: make_i32(), is_variadic: false),
    locals: [arg_local, ret_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: diagnostic_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
val result = make_simple_backend().compile(single_block_module("float_port_mod", func))
check(result.is_err())
val err = result.unwrap_err()
check(err.message.contains("f32 input port `arg0`"))
check(err.message.contains("before VHDL emission"))
check(err.has_location)
expect(err.location).to_equal("7:3-8")
```

</details>

#### rejects Unit local signal lowering before VHDL emission

1. id: BlockId
2. label: Some
3. terminator: MirTerminator Return
4. symbol: SymbolId
5. signature: MirSignature
6. entry block: BlockId entry
7. span: diagnostic span
8. check
9. check
10. check
11. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_local = make_return_local(1, make_i32())
val unit_local = make_temp_local(2, "unit_tmp", make_unit())
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 71),
    name: "unit_local",
    signature: MirSignature(params: [], return_type: make_i32(), is_variadic: false),
    locals: [ret_local, unit_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: diagnostic_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
val result = make_simple_backend().compile(single_block_module("unit_local_mod", func))
check(result.is_err())
val err = result.unwrap_err()
check(err.message.contains("Unit local signal"))
check(err.message.contains("no VHDL signal"))
check(err.has_location)
```

</details>

#### rejects pointer constants before package VHDL emission

1. symbol: SymbolId
2. type : make ptr i32
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val constant = MirConstant(
    symbol: SymbolId(id: 72),
    name: "BAD_PTR",
    type_: make_ptr_i32(),
    value: MirConstValue.Zero
)
var constants: Dict<SymbolId, MirConstant> = {}
constants[constant.symbol] = constant
val module = MirModule(name: "ptr_const_mod", functions: {}, statics: {}, constants: constants, types: {})
val result = make_simple_backend().compile(module)
check(result.is_err())
check(result.unwrap_err().message.contains("pointer constant `BAD_PTR`"))
```

</details>

#### rejects pointer memory instructions with instruction spans

1. id: BlockId
2. label: Some
3. LocalId
4. MirOperand
5. span: Some
6. terminator: MirTerminator Return
7. symbol: SymbolId
8. signature: MirSignature
9. entry block: BlockId entry
10. span: empty span
11. check
12. check
13. check
   - Expected: err.location equals `7:3-8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_local = make_return_local(1, make_i32())
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.Load(
                LocalId(id: 1),
                MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(0), make_i32()))
            ),
            span: Some(diagnostic_span())
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 73),
    name: "ptr_load",
    signature: MirSignature(params: [], return_type: make_i32(), is_variadic: false),
    locals: [ret_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
val result = make_simple_backend().compile(single_block_module("ptr_load_mod", func))
check(result.is_err())
val err = result.unwrap_err()
check(err.message.contains("pointer Load lowering"))
check(err.has_location)
expect(err.location).to_equal("7:3-8")
```

</details>

#### keeps generic call lowering and unsupported terminators as hard errors

1. id: BlockId
2. label: Some
3. MirOperand
4. terminator: MirTerminator Return
5. symbol: SymbolId
6. signature: MirSignature
7. entry block: BlockId entry
8. span: empty span
9. check
10. check
11. id: BlockId
12. label: Some
13. terminator: MirTerminator Abort
14. symbol: SymbolId
15. signature: MirSignature
16. locals: [make return local
17. entry block: BlockId entry
18. span: empty span
19. check
20. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 66 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_local = make_return_local(1, make_i32())
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.Call(
                nil,
                MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(0), make_i32())),
                []
            ),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 60),
    name: "bad_call",
    signature: MirSignature(params: [], return_type: make_i32(), is_variadic: false),
    locals: [ret_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
val backend = make_simple_backend()
val call_result = backend.compile(single_block_module("bad_call_mod", func))
check(call_result.is_err())
check(call_result.unwrap_err().message.contains("generic Call lowering"))

val abort_block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [],
    terminator: MirTerminator.Abort("boom")
)
val abort_func = MirFunction(
    symbol: SymbolId(id: 61),
    name: "bad_abort",
    signature: MirSignature(params: [], return_type: make_i32(), is_variadic: false),
    locals: [make_return_local(1, make_i32())],
    blocks: [abort_block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
val abort_result = backend.compile(single_block_module("bad_abort_mod", abort_func))
check(abort_result.is_err())
check(abort_result.unwrap_err().message.contains("Unsupported VHDL terminator"))
```

</details>

#### compiles MIR VHDL combinational processes with real block contents

1. id: BlockId
2. label: Some
3. kind: MirInstKind Copy
4. terminator: MirTerminator Return
5. id: BlockId
6. label: Some
7. VhdlProcessKind Combinational
8. BlockId
9. terminator: MirTerminator Return
10. symbol: SymbolId
11. signature: MirSignature
12. entry block: BlockId entry
13. span: empty span
14. check
15. check
16. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_local = make_arg_local(1, 0, "src_in", make_i32())
val ret_local = make_return_local(2, make_i32())
val body_block = MirBlock(
    id: BlockId(id: 1),
    label: Some("proc_body"),
    instructions: [
        MirInst(
            kind: MirInstKind.Copy(LocalId(id: 2), LocalId(id: 1)),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val entry_block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.VhdlProcess(
                VhdlProcessKind.Combinational(["src_in"]),
                BlockId(id: 1)
            ),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 30),
    name: "passthrough",
    signature: MirSignature(params: [make_i32()], return_type: make_i32(), is_variadic: false),
    locals: [src_local, ret_local],
    blocks: [entry_block, body_block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)

val backend = make_simple_backend()
val result = backend.compile(single_block_module("proc_mod", func))
check(result.is_ok())
val compiled = result.unwrap()

check(compiled.vhdl.contains("process(src_in)"))
check(compiled.vhdl.contains("result_out <= src_in;"))
```

</details>

#### rejects ambiguous fixed-width integer mismatches for bitwise operations

1. id: BlockId
2. label: Some
3. LocalId
4. MirOperand
5. MirOperand
6. terminator: MirTerminator Return
7. symbol: SymbolId
8. signature: MirSignature
9. entry block: BlockId entry
10. span: empty span
11. check
12. check
13. check
14. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left_local = make_arg_local(1, 0, "a", make_i32())
val right_local = make_arg_local(2, 1, "b", make_i64())
val ret_local = make_return_local(3, make_i32())
val temp_local = make_temp_local(4, "masked", make_i32())
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.BinOp(
                LocalId(id: 4),
                MirBinOp.BitAnd,
                MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
                MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2)))
            ),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 70),
    name: "bad_width_bitand",
    signature: MirSignature(params: [make_i32(), make_i64()], return_type: make_i32(), is_variadic: false),
    locals: [left_local, right_local, ret_local, temp_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
val result = make_simple_backend().compile(single_block_module("bad_width_bitand_mod", func))
check(result.is_err())
val err = result.unwrap_err()
check(err.message.contains("Ambiguous VHDL integer width mismatch"))
check(err.message.contains("explicit cast or VhdlResize"))
check(err.phase.contains("vhdl"))
```

</details>

#### rejects ambiguous fixed-width integer mismatches for comparisons

1. id: BlockId
2. label: Some
3. LocalId
4. MirOperand
5. MirOperand
6. terminator: MirTerminator Return
7. symbol: SymbolId
8. signature: MirSignature
9. entry block: BlockId entry
10. span: empty span
11. check
12. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left_local = make_arg_local(1, 0, "a", make_u8())
val right_local = make_arg_local(2, 1, "b", make_u32())
val ret_local = make_return_local(3, make_bool())
val cmp_local = make_temp_local(4, "cmp", make_bool())
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.BinOp(
                LocalId(id: 4),
                MirBinOp.Lt,
                MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
                MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2)))
            ),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 4)))))
)
val func = MirFunction(
    symbol: SymbolId(id: 71),
    name: "bad_width_cmp",
    signature: MirSignature(params: [make_u8(), make_u32()], return_type: make_bool(), is_variadic: false),
    locals: [left_local, right_local, ret_local, cmp_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
val result = make_simple_backend().compile(single_block_module("bad_width_cmp_mod", func))
check(result.is_err())
check(result.unwrap_err().message.contains("Ambiguous VHDL integer width mismatch"))
```

</details>

#### preserves explicit casts before fixed-width comparisons

1. id: BlockId
2. label: Some
3. LocalId
4. MirOperand
5. make i32
6. LocalId
7. MirOperand
8. MirOperand
9. terminator: MirTerminator Return
10. symbol: SymbolId
11. signature: MirSignature
12. entry block: BlockId entry
13. span: empty span
14. check
15. check
16. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left_local = make_arg_local(1, 0, "a", make_i32())
val right_local = make_arg_local(2, 1, "b", make_i64())
val ret_local = make_return_local(3, make_bool())
val narrowed_local = make_temp_local(4, "b32", make_i32())
val cmp_local = make_temp_local(5, "cmp", make_bool())
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.Cast(
                LocalId(id: 4),
                MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2))),
                make_i32()
            ),
            span: nil
        ),
        MirInst(
            kind: MirInstKind.BinOp(
                LocalId(id: 5),
                MirBinOp.Eq,
                MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
                MirOperand(kind: MirOperandKind.Copy(LocalId(id: 4)))
            ),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 5)))))
)
val func = MirFunction(
    symbol: SymbolId(id: 72),
    name: "explicit_width_cmp",
    signature: MirSignature(params: [make_i32(), make_i64()], return_type: make_bool(), is_variadic: false),
    locals: [left_local, right_local, ret_local, narrowed_local, cmp_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
val result = make_simple_backend().compile(single_block_module("explicit_width_cmp_mod", func))
check(result.is_ok())
val vhdl = result.unwrap().vhdl
check(vhdl.contains("b32 <= resize(signed(b), 32);"))
check(vhdl.contains("cmp <= '1' when a = b32 else '0';"))
```

</details>

#### maps arbitrary unsigned fixed-width bit lanes to numeric_std unsigned

1. id: BlockId
2. label: Some
3. LocalId
4. MirOperand
5. terminator: MirTerminator Return
6. symbol: SymbolId
7. signature: MirSignature
8. entry block: BlockId entry
9. span: empty span
10. check
11. check
12. check
13. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_local = make_arg_local(1, 0, "a", make_bits(9))
val ret_local = make_return_local(2, make_bits(17))
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.VhdlResize(
                LocalId(id: 2),
                MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
                17,
                false
            ),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 73),
    name: "bits_zero_extend",
    signature: MirSignature(params: [make_bits(9)], return_type: make_bits(17), is_variadic: false),
    locals: [src_local, ret_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
val result = make_simple_backend().compile(single_block_module("bits_zero_extend_mod", func))
check(result.is_ok())
val vhdl = result.unwrap().vhdl
check(vhdl.contains("a : in unsigned(8 downto 0);"))
check(vhdl.contains("result_out : out unsigned(16 downto 0)"))
check(vhdl.contains("result_out <= resize(unsigned(a), 17);"))
```

</details>

#### maps arbitrary signed fixed-width bit lanes and sign-extends resize

1. id: BlockId
2. label: Some
3. LocalId
4. MirOperand
5. terminator: MirTerminator Return
6. symbol: SymbolId
7. signature: MirSignature
8. entry block: BlockId entry
9. span: empty span
10. check
11. check
12. check
13. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_local = make_arg_local(1, 0, "a", make_sbits(9))
val ret_local = make_return_local(2, make_sbits(17))
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.VhdlResize(
                LocalId(id: 2),
                MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
                17,
                true
            ),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 74),
    name: "bits_sign_extend",
    signature: MirSignature(params: [make_sbits(9)], return_type: make_sbits(17), is_variadic: false),
    locals: [src_local, ret_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
val result = make_simple_backend().compile(single_block_module("bits_sign_extend_mod", func))
check(result.is_ok())
val vhdl = result.unwrap().vhdl
check(vhdl.contains("a : in signed(8 downto 0);"))
check(vhdl.contains("result_out : out signed(16 downto 0)"))
check(vhdl.contains("result_out <= resize(signed(a), 17);"))
```

</details>

#### emits explicit unsigned resize for named truncation

1. id: BlockId
2. label: Some
3. LocalId
4. MirOperand
5. terminator: MirTerminator Return
6. symbol: SymbolId
7. signature: MirSignature
8. entry block: BlockId entry
9. span: empty span
10. check
11. check
12. check
13. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_local = make_arg_local(1, 0, "wide", make_bits(17))
val ret_local = make_return_local(2, make_bits(5))
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.VhdlResize(
                LocalId(id: 2),
                MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
                5,
                false
            ),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 75),
    name: "bits_truncate",
    signature: MirSignature(params: [make_bits(17)], return_type: make_bits(5), is_variadic: false),
    locals: [src_local, ret_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
val result = make_simple_backend().compile(single_block_module("bits_truncate_mod", func))
check(result.is_ok())
val vhdl = result.unwrap().vhdl
check(vhdl.contains("wide : in unsigned(16 downto 0);"))
check(vhdl.contains("result_out : out unsigned(4 downto 0)"))
check(vhdl.contains("result_out <= resize(unsigned(wide), 5);"))
```

</details>

#### zero-extends VhdlSlice results into wider unsigned destinations

1. id: BlockId
2. label: Some
3. LocalId
4. MirOperand
5. terminator: MirTerminator Return
6. symbol: SymbolId
7. signature: MirSignature
8. entry block: BlockId entry
9. span: empty span
10. check
11. check
12. check
13. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_local = make_arg_local(1, 0, "imem_rdata", make_bits(32))
val ret_local = make_return_local(2, make_bits(7))
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.VhdlSlice(
                LocalId(id: 2),
                MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
                6,
                0
            ),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 751),
    name: "bitfield_opcode_slice",
    signature: MirSignature(params: [make_bits(32)], return_type: make_bits(7), is_variadic: false),
    locals: [src_local, ret_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
val result = make_simple_backend().compile(single_block_module("bitfield_opcode_slice_mod", func))
check(result.is_ok())
val vhdl = result.unwrap().vhdl
check(vhdl.contains("imem_rdata : in unsigned(31 downto 0);"))
check(vhdl.contains("result_out : out unsigned(6 downto 0)"))
check(vhdl.contains("result_out <= resize(unsigned(imem_rdata(6 downto 0)), 7);"))
```

</details>

#### casts VhdlSlice results into wider signed destinations

1. id: BlockId
2. label: Some
3. LocalId
4. MirOperand
5. terminator: MirTerminator Return
6. symbol: SymbolId
7. signature: MirSignature
8. entry block: BlockId entry
9. span: empty span
10. check
11. check
12. check
13. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_local = make_arg_local(1, 0, "status_word", make_bits(32))
val ret_local = make_return_local(2, make_sbits(7))
val block = MirBlock(
    id: BlockId(id: 0),
    label: Some("entry"),
    instructions: [
        MirInst(
            kind: MirInstKind.VhdlSlice(
                LocalId(id: 2),
                MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
                11,
                5
            ),
            span: nil
        )
    ],
    terminator: MirTerminator.Return(nil)
)
val func = MirFunction(
    symbol: SymbolId(id: 752),
    name: "bitfield_signed_slice",
    signature: MirSignature(params: [make_bits(32)], return_type: make_sbits(7), is_variadic: false),
    locals: [src_local, ret_local],
    blocks: [block],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: false,
    export_name: "",
    driver_manifest_attr: nil
)
val result = make_simple_backend().compile(single_block_module("bitfield_signed_slice_mod", func))
check(result.is_ok())
val vhdl = result.unwrap().vhdl
check(vhdl.contains("status_word : in unsigned(31 downto 0);"))
check(vhdl.contains("result_out : out signed(6 downto 0)"))
check(vhdl.contains("result_out <= resize(signed(status_word(11 downto 5)), 7);"))
```

</details>

#### lowers hardware bitfield reads through MIR VhdlSlice into typed VHDL slices

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = """
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 58 |
| Active scenarios | 58 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
