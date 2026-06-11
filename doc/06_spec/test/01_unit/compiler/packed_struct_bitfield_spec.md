# packed_struct_bitfield_spec

> FR-DRIVER-0003 — pure Simple `@packed struct { field: Type:N }` evidence.

<!-- sdn-diagram:id=packed_struct_bitfield_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=packed_struct_bitfield_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

packed_struct_bitfield_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=packed_struct_bitfield_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# packed_struct_bitfield_spec

FR-DRIVER-0003 — pure Simple `@packed struct { field: Type:N }` evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/packed_struct_bitfield_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

FR-DRIVER-0003 — pure Simple `@packed struct { field: Type:N }` evidence.

Rust remains seed/bootstrap code. These checks pin the self-hosted parser,
flat AST bridge, and driver example paths that carry the production contract.

## Scenarios

### FR-DRIVER-0003 @packed struct parser

#### self-hosted parser captures field bit widths after type annotations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/core/parser_decls_part1.spl")
expect(src.contains("T:N syntax")).to_equal(true)
expect(src.contains("fbits = parse_int_text(par_text_get())")).to_equal(true)
expect(src.contains("field_bits.push(fbits)")).to_equal(true)
```

</details>

#### self-hosted parser rejects @packed fields without bit widths

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/core/parser_decls_part2.spl")
expect(src.contains("decl_get_field_bits")).to_equal(true)
expect(src.contains("@packed struct fields must use explicit bit widths")).to_equal(true)
expect(src.contains("use an explicit nested struct instead")).to_equal(true)
```

</details>

### FR-DRIVER-0003 @packed struct lowering

#### flat AST bridge routes packed structs into module bitfields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/flat_ast_bridge_part2.spl")
expect(src.contains("decl_is_packed")).to_equal(true)
expect(src.contains("bitfields[s_name] = Bitfield")).to_equal(true)
expect(src.contains("has_bits: fb > 0")).to_equal(true)
```

</details>

#### null_block example carries a packed status register

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("examples/09_embedded/simple_os/src/drivers/null_block.spl")
expect(src.contains("@packed")).to_equal(true)
expect(src.contains("struct NullBlockStatusRegister")).to_equal(true)
expect(src.contains("ready: u32:1")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
