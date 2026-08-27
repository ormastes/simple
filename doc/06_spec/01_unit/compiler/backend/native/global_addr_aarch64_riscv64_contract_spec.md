# global_addr_aarch64_riscv64_contract_spec

> Exact native AArch64/RV64 global-address and object-layout contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# global_addr_aarch64_riscv64_contract_spec

Exact native AArch64/RV64 global-address and object-layout contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/global_addr_aarch64_riscv64_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exact native AArch64/RV64 global-address and object-layout contract.

## Scenarios

### AArch64 native global address instructions

#### uses one address identity for strings GlobalAddr loads and stores

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses one address identity for strings GlobalAddr loads and stores
- Inspect the exact ADRP plus ADD-low12 address pair
   - Expected: has(A64_ISEL, "A64_OP_ADRP, [dest, op_sym(name)]") is true
   - Expected: has(A64_ISEL, "A64_OP_ADD_IMM, [dest, dest, op_sym(name)]") is true
   - Expected: has(A64_ISEL, "A64_OP_ADD_IMM, [low.result, low.result, op_sym(label)]") is true
   - Expected: has(A64_ISEL, "a64_global_address(ctx, addr.result, symbol_id)") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
# @req REQ-SSPEC-UNIT
# @req REQ-COMPILER-NATIVE-GLOBAL-ADDR-A64-RV64-001
step("uses one address identity for strings GlobalAddr loads and stores")
step("Inspect the exact ADRP plus ADD-low12 address pair")
expect(has(A64_ISEL, "A64_OP_ADRP, [dest, op_sym(name)]")).to_equal(true)
expect(has(A64_ISEL, "A64_OP_ADD_IMM, [dest, dest, op_sym(name)]")).to_equal(true)
expect(has(A64_ISEL, "A64_OP_ADD_IMM, [low.result, low.result, op_sym(label)]")).to_equal(true)
expect(has(A64_ISEL, "a64_global_address(ctx, addr.result, symbol_id)")).to_equal(true)
```

</details>

#### encodes exact relocation types and u32 versus pointer memory forms

- encodes exact relocation types and u32 versus pointer memory forms
- Inspect exact AArch64 opcodes and relocation numbers
   - Expected: has(A64_ENCODE, "reloc_type: 277") is true
   - Expected: has(A64_ENCODE, "reloc_type: 275") is true
   - Expected: has(A64_ENCODE, "0x90000000 | rd") is true
   - Expected: has(A64_ENCODE, "0x91000000 | (((rn) << 5)) | rd") is true
   - Expected: has(A64_ENCODE, "0xB9400000") is true
   - Expected: has(A64_ENCODE, "0xB9000000") is true
   - Expected: has(A64_ISEL, "if a64_global_size(ctx, symbol_id) == 4: A64_OP_LDR_W else: A64_OP_LDR") is true
   - Expected: has(A64_ISEL, "if a64_global_size(ctx, symbol_id) == 4: A64_OP_STR_W else: A64_OP_STR") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("encodes exact relocation types and u32 versus pointer memory forms")
step("Inspect exact AArch64 opcodes and relocation numbers")
expect(has(A64_ENCODE, "reloc_type: 277")).to_equal(true)
expect(has(A64_ENCODE, "reloc_type: 275")).to_equal(true)
expect(has(A64_ENCODE, "0x90000000 | rd")).to_equal(true)
expect(has(A64_ENCODE, "0x91000000 | (((rn) << 5)) | rd")).to_equal(true)
expect(has(A64_ENCODE, "0xB9400000")).to_equal(true)
expect(has(A64_ENCODE, "0xB9000000")).to_equal(true)
expect(has(A64_ISEL, "if a64_global_size(ctx, symbol_id) == 4: A64_OP_LDR_W else: A64_OP_LDR")).to_equal(true)
expect(has(A64_ISEL, "if a64_global_size(ctx, symbol_id) == 4: A64_OP_STR_W else: A64_OP_STR")).to_equal(true)
```

</details>

### RV64 native global address relocation identity

#### uses the exact AUIPC and ADDI address pair

- uses the exact AUIPC and ADDI address pair
- Inspect RV64 PC-relative global address selection
   - Expected: has(RV64_ISEL, "RV_OP_AUIPC, [dest, op_sym(name)]") is true
   - Expected: has(RV64_ISEL, "RV_OP_ADDI, [dest, dest, op_sym(name)]") is true
   - Expected: has(RV64_ISEL, "rv64_global_address(ctx, addr.result, symbol_id)") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses the exact AUIPC and ADDI address pair")
step("Inspect RV64 PC-relative global address selection")
expect(has(RV64_ISEL, "RV_OP_AUIPC, [dest, op_sym(name)]")).to_equal(true)
expect(has(RV64_ISEL, "RV_OP_ADDI, [dest, dest, op_sym(name)]")).to_equal(true)
expect(has(RV64_ISEL, "rv64_global_address(ctx, addr.result, symbol_id)")).to_equal(true)
```

</details>

#### anchors low12 at the paired AUIPC and emits exact relocation types

- anchors low12 at the paired AUIPC and emits exact relocation types
- Inspect HI20 target identity and LO12 local-anchor identity
   - Expected: has(RV64_ENCODE, "reloc_type: 23") is true
   - Expected: has(RV64_ENCODE, "reloc_type: 24") is true
   - Expected: has(RV64_ENCODE, "anchor_offset: reloc_offset - 4") is true
   - Expected: has(ELF, "Riscv_PcrelHi20") is true
   - Expected: has(ELF, "Riscv_PcrelLo12I") is true
   - Expected: has(ELF, "reloc.anchor_offset < 0") is true
   - Expected: has(ELF, "anchor_offsets_r[relocation_symbol] = code_start + reloc.anchor_offset") is true
   - Expected: has(ELF, "sym_type: ElfSymbolType.NoType, section_index: 1") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("anchors low12 at the paired AUIPC and emits exact relocation types")
step("Inspect HI20 target identity and LO12 local-anchor identity")
expect(has(RV64_ENCODE, "reloc_type: 23")).to_equal(true)
expect(has(RV64_ENCODE, "reloc_type: 24")).to_equal(true)
expect(has(RV64_ENCODE, "anchor_offset: reloc_offset - 4")).to_equal(true)
expect(has(ELF, "Riscv_PcrelHi20")).to_equal(true)
expect(has(ELF, "Riscv_PcrelLo12I")).to_equal(true)
expect(has(ELF, "reloc.anchor_offset < 0")).to_equal(true)
expect(has(ELF, "anchor_offsets_r[relocation_symbol] = code_start + reloc.anchor_offset")).to_equal(true)
expect(has(ELF, "sym_type: ElfSymbolType.NoType, section_index: 1")).to_equal(true)
```

</details>

#### selects exact u32 and pointer load-store widths

- selects exact u32 and pointer load-store widths
- Inspect LW/SW and LD/SD selection
   - Expected: has(RV64_ISEL, "if rv64_global_size(ctx, symbol_id) == 8: RV_OP_LD elif signed: RV_OP_LW else: RV_OP_LWU") is true
   - Expected: has(RV64_ENCODE, "riscv_encode_i_type(offset, base, 6, rd, 0x03)") is true
   - Expected: has(RV64_ISEL, "if rv64_global_size(ctx, symbol_id) == 4: RV_OP_SW else: RV_OP_SD") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("selects exact u32 and pointer load-store widths")
step("Inspect LW/SW and LD/SD selection")
expect(has(RV64_ISEL, "if rv64_global_size(ctx, symbol_id) == 8: RV_OP_LD elif signed: RV_OP_LW else: RV_OP_LWU")).to_equal(true)
expect(has(RV64_ENCODE, "riscv_encode_i_type(offset, base, 6, rd, 0x03)")).to_equal(true)
expect(has(RV64_ISEL, "if rv64_global_size(ctx, symbol_id) == 4: RV_OP_SW else: RV_OP_SD")).to_equal(true)
```

</details>

### native AArch64 and RV64 static admission MC/DC

#### accepts only u32-compatible and pointer-like storage

- accepts only u32-compatible and pointer-like storage
- Exercise supported and unsupported type decisions
   - Expected: a64_static_type_supported(u32_type) is true
   - Expected: a64_static_type_supported(ptr_type) is true
   - Expected: a64_static_type_supported(bad_type) is false
   - Expected: rv64_static_type_supported(u32_type) is true
   - Expected: rv64_static_type_supported(ptr_type) is true
   - Expected: rv64_static_type_supported(bad_type) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts only u32-compatible and pointer-like storage")
step("Exercise supported and unsupported type decisions")
val u32_type = MirType(kind: MirTypeKind.U32)
val ptr_type = MirType(kind: MirTypeKind.Ptr(u32_type, false))
val bad_type = MirType(kind: MirTypeKind.F32)
expect(a64_static_type_supported(u32_type)).to_equal(true)
expect(a64_static_type_supported(ptr_type)).to_equal(true)
expect(a64_static_type_supported(bad_type)).to_equal(false)
expect(rv64_static_type_supported(u32_type)).to_equal(true)
expect(rv64_static_type_supported(ptr_type)).to_equal(true)
expect(rv64_static_type_supported(bad_type)).to_equal(false)
```

</details>

#### covers natural explicit invalid and under-aligned decisions

- covers natural explicit invalid and under-aligned decisions
- Exercise alignment decisions independently
   - Expected: accepted is true
   - Expected: rejected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("covers natural explicit invalid and under-aligned decisions")
step("Exercise alignment decisions independently")
for accepted in [a64_static_alignment_valid(4, 0), a64_static_alignment_valid(4, 8), rv64_static_alignment_valid(4, 0), rv64_static_alignment_valid(4, 8)]:
    expect(accepted).to_equal(true)
for rejected in [a64_static_alignment_valid(4, -1), a64_static_alignment_valid(4, 3), a64_static_alignment_valid(8, 4), rv64_static_alignment_valid(4, -1), rv64_static_alignment_valid(4, 3), rv64_static_alignment_valid(8, 4)]:
    expect(rejected).to_equal(false)
```

</details>

#### covers immutable read mutable-address and store admission

- covers immutable read mutable-address and store admission
- Exercise mutability and requested-write conditions independently
   - Expected: admitted is true
   - Expected: a64_static_write_admitted(false, true) is false
   - Expected: rv64_static_write_admitted(false, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("covers immutable read mutable-address and store admission")
step("Exercise mutability and requested-write conditions independently")
for admitted in [a64_static_write_admitted(false, false), a64_static_write_admitted(true, false), a64_static_write_admitted(true, true), rv64_static_write_admitted(false, false), rv64_static_write_admitted(true, false), rv64_static_write_admitted(true, true)]:
    expect(admitted).to_equal(true)
expect(a64_static_write_admitted(false, true)).to_equal(false)
expect(rv64_static_write_admitted(false, true)).to_equal(false)
```

</details>

#### rejects every nonzero spill demand

- rejects every nonzero spill demand
- Exercise the production no-spill admission boundary
   - Expected: target_no_spill_admitted(0) is true
   - Expected: target_no_spill_admitted(1) is false
   - Expected: target_no_spill_admitted(12) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects every nonzero spill demand")
step("Exercise the production no-spill admission boundary")
expect(target_no_spill_admitted(0)).to_equal(true)
expect(target_no_spill_admitted(1)).to_equal(false)
expect(target_no_spill_admitted(12)).to_equal(false)
```

</details>

#### rejects invalid initializers missing metadata and orphan low anchors

- rejects invalid initializers missing metadata and orphan low anchors
- Exercise fail-closed pipeline admission predicates
   - Expected: a64_static_initializer_supported(MirConstValue.Int(1)) is true
   - Expected: a64_static_initializer_supported(MirConstValue.Zero) is true
   - Expected: a64_static_initializer_supported(MirConstValue.Str("bad")) is false
   - Expected: rv64_static_initializer_supported(MirConstValue.Int(1)) is true
   - Expected: rv64_static_initializer_supported(MirConstValue.Zero) is true
   - Expected: rv64_static_initializer_supported(MirConstValue.Str("bad")) is false
   - Expected: a64_global_metadata_present(new_isel_context(), 99) is false
   - Expected: rv64_global_metadata_present(new_isel_context(), 99) is false
   - Expected: rv64_pcrel_low_anchor_valid(-1) is false
   - Expected: rv64_pcrel_low_anchor_valid(2) is false
   - Expected: rv64_pcrel_low_anchor_valid(0) is true
   - Expected: rv64_pcrel_low_anchor_valid(16) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects invalid initializers missing metadata and orphan low anchors")
step("Exercise fail-closed pipeline admission predicates")
expect(a64_static_initializer_supported(MirConstValue.Int(1))).to_equal(true)
expect(a64_static_initializer_supported(MirConstValue.Zero)).to_equal(true)
expect(a64_static_initializer_supported(MirConstValue.Str("bad"))).to_equal(false)
expect(rv64_static_initializer_supported(MirConstValue.Int(1))).to_equal(true)
expect(rv64_static_initializer_supported(MirConstValue.Zero)).to_equal(true)
expect(rv64_static_initializer_supported(MirConstValue.Str("bad"))).to_equal(false)
expect(a64_global_metadata_present(new_isel_context(), 99)).to_equal(false)
expect(rv64_global_metadata_present(new_isel_context(), 99)).to_equal(false)
expect(rv64_pcrel_low_anchor_valid(-1)).to_equal(false)
expect(rv64_pcrel_low_anchor_valid(2)).to_equal(false)
expect(rv64_pcrel_low_anchor_valid(0)).to_equal(true)
expect(rv64_pcrel_low_anchor_valid(16)).to_equal(true)
```

</details>

### target allocator loop pressure

<details>
<summary>Advanced: does not merge sixteen sequential loop temporaries into one live set</summary>

#### does not merge sixteen sequential loop temporaries into one live set

- does not merge sixteen sequential loop temporaries into one live set
- Allocate a backedge loop wider than either target register set
   - Expected: a64.functions[0].used_callee_saved.len() <= 2 is true
   - Expected: rv64.functions[0].used_callee_saved.len() <= 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not merge sixteen sequential loop temporaries into one live set")
step("Allocate a backedge loop wider than either target register set")
val a64 = regalloc_module_aarch64(sequential_loop_module(true))
val rv64 = regalloc_module_riscv64(sequential_loop_module(false))
expect(a64.functions[0].used_callee_saved.len() <= 2).to_equal(true)
expect(rv64.functions[0].used_callee_saved.len() <= 2).to_equal(true)
```

</details>


</details>

### native AArch64 and RV64 ELF data ownership

#### uses solved aligned data and rodata layouts and exact symbol ordinals

- uses solved aligned data and rodata layouts and exact symbol ordinals
- Inspect shared layout, linkage, offsets, and section ordinals
   - Expected: has(ELF, "solve_native_data_layout(module.data_sections, true)") is true
   - Expected: has(ELF, "solve_native_data_layout(module.data_sections, false)") is true
   - Expected: has(ELF, "new_rodata_section_aligned(rodata_layout_a.bytes, rodata_layout_a.max_alignment)") is true
   - Expected: has(ELF, "new_data_section_aligned(data_layout_a.bytes, data_layout_a.max_alignment)") is true
   - Expected: has(ELF, "new_rodata_section_aligned(rodata_layout_r.bytes, rodata_layout_r.max_alignment)") is true
   - Expected: has(ELF, "new_data_section_aligned(data_layout_r.bytes, data_layout_r.max_alignment)") is true
   - Expected: has(ELF, "val data_section_index_a = 2") is true
   - Expected: has(ELF, "val data_section_index_r = 2") is true
   - Expected: has(ELF, "sym_bind: if entry.is_global: ElfSymbolBind.Global else: ElfSymbolBind.Local") is true
   - Expected: has(ELF, "panic(\"aarch64 ELF relocation references unknown symbol") is true
   - Expected: has(ELF, "panic(\"riscv64 ELF relocation references unknown symbol") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses solved aligned data and rodata layouts and exact symbol ordinals")
step("Inspect shared layout, linkage, offsets, and section ordinals")
for suffix in ["a", "r"]:
    expect(has(ELF, "solve_native_data_layout(module.data_sections, true)")).to_equal(true)
    expect(has(ELF, "solve_native_data_layout(module.data_sections, false)")).to_equal(true)
expect(has(ELF, "new_rodata_section_aligned(rodata_layout_a.bytes, rodata_layout_a.max_alignment)")).to_equal(true)
expect(has(ELF, "new_data_section_aligned(data_layout_a.bytes, data_layout_a.max_alignment)")).to_equal(true)
expect(has(ELF, "new_rodata_section_aligned(rodata_layout_r.bytes, rodata_layout_r.max_alignment)")).to_equal(true)
expect(has(ELF, "new_data_section_aligned(data_layout_r.bytes, data_layout_r.max_alignment)")).to_equal(true)
expect(has(ELF, "val data_section_index_a = 2")).to_equal(true)
expect(has(ELF, "val data_section_index_r = 2")).to_equal(true)
expect(has(ELF, "sym_bind: if entry.is_global: ElfSymbolBind.Global else: ElfSymbolBind.Local")).to_equal(true)
expect(has(ELF, "panic(\"aarch64 ELF relocation references unknown symbol")).to_equal(true)
expect(has(ELF, "panic(\"riscv64 ELF relocation references unknown symbol")).to_equal(true)
```

</details>

### executable AArch64 MIR to ELF global ownership

#### allocates encodes and parses exact address relocations and objects

- allocates encodes and parses exact address relocations and objects
- Lower constructed MIR through AArch64 allocation, encoding, and ELF parsing
   - Expected: relocation_count(parsed, 275) equals `6`
   - Expected: relocation_count(parsed, 277) equals `6`
   - Expected: elf_symbol_binding(symbol) equals `STB_GLOBAL`
   - Expected: elf_symbol_type(symbol) equals `STT_OBJECT`
   - Expected: symbol.st_shndx equals `2`
   - Expected: symbol.st_size equals `4`
   - Expected: symbol.st_value equals `0`
   - Expected: elf_symbol_binding(symbol) equals `STB_LOCAL`
   - Expected: elf_symbol_type(symbol) equals `STT_OBJECT`
   - Expected: symbol.st_shndx equals `3`
   - Expected: symbol.st_size equals `8`
   - Expected: symbol.st_value equals `0`
   - Expected: counter_seen is true
   - Expected: root_seen is true
   - Expected: parsed.sections[2].sh_flags equals `3`
   - Expected: parsed.sections[3].sh_flags equals `2`
   - Expected: kind == 275 or kind == 277 is true
   - Expected: parsed.symbols[elf_reloc_sym(reloc)].name.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allocates encodes and parses exact address relocations and objects")
step("Lower constructed MIR through AArch64 allocation, encoding, and ELF parsing")
val mir = executable_global_module()
val selected = isel_module_aarch64(mir)
val allocated = regalloc_module_aarch64(selected)
val encoded = encode_module_aarch64(allocated)
for reloc in encoded[0].relocations:
    if reloc.reloc_type == 275: expect(encoded[0].code[reloc.offset + 3]).to_equal(0x90)
    elif reloc.reloc_type == 277: expect(encoded[0].code[reloc.offset + 3]).to_equal(0x91)
val parsed = elf_parse_object(bytes_u8(emit_elf_aarch64(encoded, allocated, mir))).unwrap()
expect(relocation_count(parsed, 275)).to_equal(6)
expect(relocation_count(parsed, 277)).to_equal(6)
var counter_seen = false
var root_seen = false
for symbol in parsed.symbols:
    if symbol.name == "counter32":
        counter_seen = true
        expect(elf_symbol_binding(symbol)).to_equal(STB_GLOBAL)
        expect(elf_symbol_type(symbol)).to_equal(STT_OBJECT)
        expect(symbol.st_shndx).to_equal(2)
        expect(symbol.st_size).to_equal(4)
        expect(symbol.st_value).to_equal(0)
    elif symbol.name == "root_ptr":
        root_seen = true
        expect(elf_symbol_binding(symbol)).to_equal(STB_LOCAL)
        expect(elf_symbol_type(symbol)).to_equal(STT_OBJECT)
        expect(symbol.st_shndx).to_equal(3)
        expect(symbol.st_size).to_equal(8)
        expect(symbol.st_value).to_equal(0)
expect(counter_seen).to_equal(true)
expect(root_seen).to_equal(true)
expect(parsed.sections[2].sh_flags).to_equal(3)
expect(parsed.sections[3].sh_flags).to_equal(2)
for index in 0..parsed.relocations.len():
    val reloc = parsed.relocations[index]
    val kind = elf_reloc_type(reloc)
    expect(kind == 275 or kind == 277).to_equal(true)
    expect(parsed.symbols[elf_reloc_sym(reloc)].name.len() > 0).to_equal(true)
```

</details>

#### saves after frame allocation and restores before resetting sp to x29

- saves after frame allocation and restores before resetting sp to x29
- Inspect exact allocated AArch64 prologue and epilogue ordering
   - Expected: saved equals `used`
   - Expected: restored equals `used`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("saves after frame allocation and restores before resetting sp to x29")
step("Inspect exact allocated AArch64 prologue and epilogue ordering")
val allocated = regalloc_module_aarch64(isel_module_aarch64(executable_global_module()))
val used = allocated.functions[0].used_callee_saved.len()
var saved = 0
var restored = 0
for block in allocated.functions[0].blocks:
    for index in 0..block.insts.len():
        val inst = block.insts[index]
        if block.block_id == -1 and inst.opcode == A64_OP_STR: saved = saved + 1
        if inst.opcode == A64_OP_MOV and inst.operands.len() >= 2:
            match inst.operands[0].kind:
                case Reg(dst):
                    match inst.operands[1].kind:
                        case Reg(src):
                            match dst.kind:
                                case Physical(dst_id):
                                    match src.kind:
                                        case Physical(src_id):
                                            if dst_id == AARCH64_SP and src_id == AARCH64_X29:
                                                var cursor = index - 1
                                                while cursor >= 0 and block.insts[cursor].opcode == A64_OP_LDR:
                                                    restored = restored + 1
                                                    cursor = cursor - 1
                                        case _: ()
                                case _: ()
                        case _: ()
                case _: ()
expect(saved).to_equal(used)
expect(restored).to_equal(used)
```

</details>

### executable RV64 MIR to ELF global ownership

#### allocates encodes and anchors every low relocation at its AUIPC

- allocates encodes and anchors every low relocation at its AUIPC
- Lower constructed MIR through RV64 allocation, encoding, and ELF parsing
   - Expected: saw_lwu is true
   - Expected: encoded[0].code[reloc.offset] % 128 equals `0x13`
   - Expected: reloc.anchor_offset + 4 equals `reloc.offset`
   - Expected: relocation_count(parsed, 23) equals `6`
   - Expected: relocation_count(parsed, 24) equals `6`
   - Expected: symbol.name.starts_with(".Lrv64.pcrel.global_roundtrip.") is true
   - Expected: symbol.st_shndx equals `1`
   - Expected: symbol.st_value + 4 equals `reloc.r_offset`
   - Expected: symbol.name == "counter32" or symbol.name == "root_ptr" or symbol.name.starts_with(".LC") is true
   - Expected: low_count equals `6`
   - Expected: elf_symbol_binding(symbol) equals `STB_GLOBAL`
   - Expected: symbol.st_shndx equals `2`
   - Expected: symbol.st_size equals `4`
   - Expected: elf_symbol_binding(symbol) equals `STB_LOCAL`
   - Expected: symbol.st_shndx equals `3`
   - Expected: symbol.st_size equals `8`
   - Expected: counter_seen is true
   - Expected: root_seen is true
   - Expected: parsed.sections[2].sh_flags equals `3`
   - Expected: parsed.sections[3].sh_flags equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allocates encodes and anchors every low relocation at its AUIPC")
step("Lower constructed MIR through RV64 allocation, encoding, and ELF parsing")
val mir = executable_global_module()
val selected = isel_module_riscv64(mir)
val allocated = regalloc_module_riscv64(selected)
val encoded = encode_module_riscv64(allocated)
var saw_lwu = false
for offset in 0..(encoded[0].code.len() / 4):
    val word = u32_le(encoded[0].code, offset * 4)
    if word % 128 == 0x03 and (word / 4096) % 8 == 6: saw_lwu = true
expect(saw_lwu).to_equal(true)
for reloc in encoded[0].relocations:
    if reloc.reloc_type == 23: expect(encoded[0].code[reloc.offset] % 128).to_equal(0x17)
    elif reloc.reloc_type == 24:
        expect(encoded[0].code[reloc.offset] % 128).to_equal(0x13)
        expect(reloc.anchor_offset + 4).to_equal(reloc.offset)
val parsed = elf_parse_object(bytes_u8(emit_elf_riscv64(encoded, allocated, mir))).unwrap()
expect(relocation_count(parsed, 23)).to_equal(6)
expect(relocation_count(parsed, 24)).to_equal(6)
var low_count = 0
for reloc in parsed.relocations:
    val symbol = parsed.symbols[elf_reloc_sym(reloc)]
    if elf_reloc_type(reloc) == 24:
        low_count = low_count + 1
        expect(symbol.name.starts_with(".Lrv64.pcrel.global_roundtrip.")).to_equal(true)
        expect(symbol.st_shndx).to_equal(1)
        expect(symbol.st_value + 4).to_equal(reloc.r_offset)
    elif elf_reloc_type(reloc) == 23:
        expect(symbol.name == "counter32" or symbol.name == "root_ptr" or symbol.name.starts_with(".LC")).to_equal(true)
expect(low_count).to_equal(6)
var counter_seen = false
var root_seen = false
for symbol in parsed.symbols:
    if symbol.name == "counter32":
        counter_seen = true
        expect(elf_symbol_binding(symbol)).to_equal(STB_GLOBAL)
        expect(symbol.st_shndx).to_equal(2)
        expect(symbol.st_size).to_equal(4)
    elif symbol.name == "root_ptr":
        root_seen = true
        expect(elf_symbol_binding(symbol)).to_equal(STB_LOCAL)
        expect(symbol.st_shndx).to_equal(3)
        expect(symbol.st_size).to_equal(8)
expect(counter_seen).to_equal(true)
expect(root_seen).to_equal(true)
expect(parsed.sections[2].sh_flags).to_equal(3)
expect(parsed.sections[3].sh_flags).to_equal(2)
```

</details>

#### restores allocator-owned callee saves before selector-owned ra and s0

- restores allocator-owned callee saves before selector-owned ra and s0
- Inspect the executable allocated RV64 epilogue order
   - Expected: block.insts[index - 1].opcode equals `RV_OP_ADDI`
   - Expected: callee_loads equals `used`
   - Expected: block.insts[index + 1].opcode equals `RV_OP_LD`
   - Expected: saw_ra_restore is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("restores allocator-owned callee saves before selector-owned ra and s0")
step("Inspect the executable allocated RV64 epilogue order")
val allocated = regalloc_module_riscv64(isel_module_riscv64(executable_global_module()))
var saw_ra_restore = false
val used = allocated.functions[0].used_callee_saved.len()
var save_size = used * 8
if save_size % 16 != 0: save_size = save_size + (16 - (save_size % 16))
for block in allocated.functions[0].blocks:
    for index in 1..block.insts.len():
        val inst = block.insts[index]
        if inst.opcode == RV_OP_LD and inst.operands.len() >= 1:
            match inst.operands[0].kind:
                case Reg(reg):
                    match reg.kind:
                        case Physical(id):
                            if id == RV_X1:
                                saw_ra_restore = true
                                expect(block.insts[index - 1].opcode).to_equal(RV_OP_ADDI)
                                match block.insts[index - 1].operands[2].kind:
                                    case Imm(value): expect(value).to_equal(save_size)
                                    case _: expect(false).to_equal(true)
                                var callee_loads = 0
                                var cursor = index - 2
                                while cursor >= 0 and block.insts[cursor].opcode == RV_OP_LD:
                                    callee_loads = callee_loads + 1
                                    cursor = cursor - 1
                                expect(callee_loads).to_equal(used)
                                match inst.operands[1].kind:
                                    case Mem(_, offset): expect(offset).to_equal(allocated.functions[0].frame_size - save_size - 8)
                                    case _: expect(false).to_equal(true)
                                expect(block.insts[index + 1].opcode).to_equal(RV_OP_LD)
                                match block.insts[index + 1].operands[1].kind:
                                    case Mem(_, offset): expect(offset).to_equal(allocated.functions[0].frame_size - save_size - 16)
                                    case _: expect(false).to_equal(true)
                        case _: ()
                case _: ()
expect(saw_ra_restore).to_equal(true)
```

</details>

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
- `REQ-COMPILER-NATIVE-GLOBAL-ADDR-A64-RV64-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f451bc8660b88a258b6316f93b80e7affb69cf6d7cf65e916a7abfcc551ea35e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f451bc8660b88a258b6316f93b80e7affb69cf6d7cf65e916a7abfcc551ea35e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f451bc8660b88a258b6316f93b80e7affb69cf6d7cf65e916a7abfcc551ea35e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/native/global_addr_aarch64_riscv64_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/native/global_addr_aarch64_riscv64_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/native/global_addr_aarch64_riscv64_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/native/global_addr_aarch64_riscv64_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/native/global_addr_aarch64_riscv64_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/native/global_addr_aarch64_riscv64_contract_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses one address identity for strings GlobalAddr loads and stores' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native/global_addr_aarch64_riscv64_contract_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes exact relocation types and u32 versus pointer memory forms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native/global_addr_aarch64_riscv64_contract_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the exact AUIPC and ADDI address pair' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
