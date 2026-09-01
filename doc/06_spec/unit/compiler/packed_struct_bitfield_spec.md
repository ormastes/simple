# packed_struct_bitfield_spec

> FR-DRIVER-0003 — pure Simple `@packed struct { field: Type:N }` evidence.

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
| Source | `test/unit/compiler/packed_struct_bitfield_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

FR-DRIVER-0003 — pure Simple `@packed struct { field: Type:N }` evidence.

Rust remains seed/bootstrap code. These checks pin the self-hosted parser,
flat AST bridge, and driver example paths that carry the production contract.

## Scenarios

### FR-DRIVER-0003 @packed struct parser

#### self-hosted parser captures field bit widths after type annotations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- self-hosted parser captures field bit widths after type annotations
   - Expected: src contains `var fbits: i64 = -1`
   - Expected: src contains `fbits = parse_int_text(par_text_get())`
   - Expected: src contains `parser_error("expected integer bit width after ':'")`
   - Expected: src contains `field_bits.push(fbits)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("self-hosted parser captures field bit widths after type annotations")
val src = read_text("src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl")
# Anchored to real parser code; the "# T:N syntax — e.g. u32:16"
# comment must not be able to satisfy this.
expect(src.contains("var fbits: i64 = -1")).to_equal(true)
expect(src.contains("fbits = parse_int_text(par_text_get())")).to_equal(true)
expect(src.contains("parser_error(\"expected integer bit width after ':'\")")).to_equal(true)
expect(src.contains("field_bits.push(fbits)")).to_equal(true)
```

</details>

#### self-hosted parser rejects @packed fields without bit widths

- self-hosted parser rejects @packed fields without bit widths
   - Expected: src contains `decl_get_field_bits`
   - Expected: src contains `@packed struct fields must use explicit bit widths`
   - Expected: src contains `use an explicit nested struct instead`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("self-hosted parser rejects @packed fields without bit widths")
val src = read_text("src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl")
expect(src.contains("decl_get_field_bits")).to_equal(true)
expect(src.contains("@packed struct fields must use explicit bit widths")).to_equal(true)
expect(src.contains("use an explicit nested struct instead")).to_equal(true)
```

</details>

### FR-DRIVER-0003 @packed struct lowering

#### flat AST bridge routes packed structs into module bitfields

- flat AST bridge routes packed structs into module bitfields
   - Expected: src contains `decl_is_packed`
   - Expected: src contains `bitfields[s_name] = Bitfield`
   - Expected: src contains `has_bits: fb > 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flat AST bridge routes packed structs into module bitfields")
val src = read_text("src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl")
expect(src.contains("decl_is_packed")).to_equal(true)
expect(src.contains("bitfields[s_name] = Bitfield")).to_equal(true)
expect(src.contains("has_bits: fb > 0")).to_equal(true)
```

</details>

#### null_block driver carries a packed status register

- null_block driver carries a packed status register
   - Expected: src contains `struct NullBlockStatusRegister`
   - Expected: src contains `@packed`
   - Expected: src contains `ready: u32:1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("null_block driver carries a packed status register")
# STALE PATH + REAL DEFECT (2026-08-10). This read
# examples/09_embedded/simple_os/src/drivers/null_block.spl, which does
# not exist and has no git history — so read_text returned "" and all
# three needles failed on an absent file rather than on the product.
# NullBlockStatusRegister actually lives in the path below now, and the
# move DROPPED the feature under test: the struct lost its `@packed`
# annotation and its `:1` bit widths, so FR-DRIVER-0003's only bitfield
# consumer no longer exercises bitfields at all. Repointed at the real
# file; LEFT RED because the capability is genuinely gone. See
# doc/08_tracking/bug/null_block_status_register_lost_packed_bitfields_2026-08-10.md
val src = read_text("src/lib/nogc_sync_mut/driver/null_block_driver.spl")
expect(src.contains("struct NullBlockStatusRegister")).to_equal(true)
expect(src.contains("@packed")).to_equal(true)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `27ff90e06c15ac0a09c71421aeb76c8746719e0a92f246a47fc0fb7ee5ea063c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `27ff90e06c15ac0a09c71421aeb76c8746719e0a92f246a47fc0fb7ee5ea063c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `27ff90e06c15ac0a09c71421aeb76c8746719e0a92f246a47fc0fb7ee5ea063c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/packed_struct_bitfield_spec.spl
mirror: doc/06_spec/unit/compiler/packed_struct_bitfield_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/packed_struct_bitfield_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/packed_struct_bitfield_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/packed_struct_bitfield_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'self-hosted parser captures field bit widths after type annotations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/packed_struct_bitfield_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'self-hosted parser rejects @packed fields without bit widths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/packed_struct_bitfield_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flat AST bridge routes packed structs into module bitfields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
