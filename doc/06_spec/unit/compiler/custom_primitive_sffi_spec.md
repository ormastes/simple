# custom_primitive_sffi_spec

> Purpose: Prove that Custom primitive SFFI metadata.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# custom_primitive_sffi_spec

Purpose: Prove that Custom primitive SFFI metadata.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/custom_primitive_sffi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Custom primitive SFFI metadata.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Custom primitive SFFI metadata

#### maps u32 wrapper metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps u32 wrapper metadata
- Verify: maps u32 wrapper metadata
   - Expected: p.signedness equals `unsigned`
   - Expected: p.bit_width equals `32`
   - Expected: p.byte_size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps u32 wrapper metadata")
step("Verify: maps u32 wrapper metadata")
# @req: REQ-COMP-CUSTOM-PRIMITIVE-SFFI-METADATA-001
val p = PrimInfo.create("MyU32", "u32")
expect(p.signedness).to_equal("unsigned")
expect(p.bit_width).to_equal(32)
expect(p.byte_size).to_equal(4)
```

</details>

#### maps i64 wrapper metadata

- maps i64 wrapper metadata
- Verify: maps i64 wrapper metadata
   - Expected: p.signedness equals `signed`
   - Expected: p.bit_width equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps i64 wrapper metadata")
step("Verify: maps i64 wrapper metadata")
val p = PrimInfo.create("MyI64", "i64")
expect(p.signedness).to_equal("signed")
expect(p.bit_width).to_equal(64)
```

</details>

#### maps bool wrapper as non-integer

- maps bool wrapper as non-integer
- Verify: maps bool wrapper as non-integer
   - Expected: p.bit_width equals `8`
   - Expected: p.is_integer() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps bool wrapper as non-integer")
step("Verify: maps bool wrapper as non-integer")
val p = PrimInfo.create("MyBool", "bool")
expect(p.bit_width).to_equal(8)
expect(p.is_integer()).to_equal(false)
```

</details>

#### marks wrapper as custom primitive

- marks wrapper as custom primitive
- Verify: marks wrapper as custom primitive
   - Expected: p.is_custom() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks wrapper as custom primitive")
step("Verify: marks wrapper as custom primitive")
val p = PrimInfo.create("Anything", "u32")
expect(p.is_custom()).to_equal(true)
```

</details>

#### returns underlying ABI type

- returns underlying ABI type
- Verify: returns underlying ABI type
   - Expected: p.abi_type() equals `u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns underlying ABI type")
step("Verify: returns underlying ABI type")
val p = PrimInfo.create("Handle", "u64")
expect(p.abi_type()).to_equal("u64")
```

</details>

### Custom primitive SFFI ABI mapping

#### maps u32 to C ABI type

- maps u32 to C ABI type
- Verify: maps u32 to C ABI type
   - Expected: m.map_c("u32") equals `uint32_t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps u32 to C ABI type")
step("Verify: maps u32 to C ABI type")
val m = AbiMap(dummy: 0)
expect(m.map_c("u32")).to_equal("uint32_t")
```

</details>

#### maps i64 to Rust ABI type

- maps i64 to Rust ABI type
- Verify: maps i64 to Rust ABI type
   - Expected: m.map_rust("i64") equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps i64 to Rust ABI type")
step("Verify: maps i64 to Rust ABI type")
val m = AbiMap(dummy: 0)
expect(m.map_rust("i64")).to_equal("i64")
```

</details>

#### maps f64 to LLVM ABI type

- maps f64 to LLVM ABI type
- Verify: maps f64 to LLVM ABI type
   - Expected: m.map_llvm("f64") equals `double`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps f64 to LLVM ABI type")
step("Verify: maps f64 to LLVM ABI type")
val m = AbiMap(dummy: 0)
expect(m.map_llvm("f64")).to_equal("double")
```

</details>

### Custom primitive bitfield validation

#### accepts u32 backing

- accepts u32 backing
- Verify: accepts u32 backing
   - Expected: BitfieldCheck.check_backing("u32") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts u32 backing")
step("Verify: accepts u32 backing")
expect(BitfieldCheck.check_backing("u32")).to_equal(true)
```

</details>

#### accepts u8 backing

- accepts u8 backing
- Verify: accepts u8 backing
   - Expected: BitfieldCheck.check_backing("u8") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts u8 backing")
step("Verify: accepts u8 backing")
expect(BitfieldCheck.check_backing("u8")).to_equal(true)
```

</details>

#### rejects f32 backing

- rejects f32 backing
- Verify: rejects f32 backing
   - Expected: BitfieldCheck.check_backing("f32") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects f32 backing")
step("Verify: rejects f32 backing")
expect(BitfieldCheck.check_backing("f32")).to_equal(false)
```

</details>

#### rejects bool backing

- rejects bool backing
- Verify: rejects bool backing
   - Expected: BitfieldCheck.check_backing("bool") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects bool backing")
step("Verify: rejects bool backing")
expect(BitfieldCheck.check_backing("bool")).to_equal(false)
```

</details>

#### accepts bounded integer field

- accepts bounded integer field
- Verify: accepts bounded integer field
   - Expected: BitfieldCheck.check_field("u16", 4, 16) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts bounded integer field")
step("Verify: accepts bounded integer field")
expect(BitfieldCheck.check_field("u16", 4, 16)).to_equal(true)
```

</details>

#### rejects field overflow

- rejects field overflow
- Verify: rejects field overflow
   - Expected: BitfieldCheck.check_field("u8", 12, 8) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects field overflow")
step("Verify: rejects field overflow")
expect(BitfieldCheck.check_field("u8", 12, 8)).to_equal(false)
```

</details>

#### rejects float field

- rejects float field
- Verify: rejects float field
   - Expected: BitfieldCheck.check_field("f32", 8, 32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects float field")
step("Verify: rejects float field")
expect(BitfieldCheck.check_field("f32", 8, 32)).to_equal(false)
```

</details>

#### accepts one-bit bool field

- accepts one-bit bool field
- Verify: accepts one-bit bool field
   - Expected: BitfieldCheck.check_field("bool", 1, 32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts one-bit bool field")
step("Verify: accepts one-bit bool field")
expect(BitfieldCheck.check_field("bool", 1, 32)).to_equal(true)
```

</details>

### Custom primitive classification and domain wrappers

#### migrates convertible primitives

- migrates convertible primitives
- Verify: migrates convertible primitives
   - Expected: c.should_migrate() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("migrates convertible primitives")
step("Verify: migrates convertible primitives")
val c = PrimClass(classification: "convertible")
expect(c.should_migrate()).to_equal(true)
```

</details>

#### does not migrate blocked primitives

- does not migrate blocked primitives
- Verify: does not migrate blocked primitives
   - Expected: c.should_migrate() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not migrate blocked primitives")
step("Verify: does not migrate blocked primitives")
val c = PrimClass(classification: "blocked")
expect(c.should_migrate()).to_equal(false)
```

</details>

#### models file handle wrapper

- models file handle wrapper
- Verify: models file handle wrapper
   - Expected: p.underlying equals `u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("models file handle wrapper")
step("Verify: models file handle wrapper")
val p = PrimInfo.create("FileHandle", "u32")
expect(p.underlying).to_equal("u32")
```

</details>

#### models IRQ vector wrapper

- models IRQ vector wrapper
- Verify: models IRQ vector wrapper
   - Expected: p.underlying equals `u16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("models IRQ vector wrapper")
step("Verify: models IRQ vector wrapper")
val p = PrimInfo.create("IrqVector", "u16")
expect(p.underlying).to_equal("u16")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-CUSTOM-PRIMITIVE-SFFI-METADATA-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `abc9f69ae4bb93e033482b9876d12452ecc89b2226b5bcef89999d20296610db`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `abc9f69ae4bb93e033482b9876d12452ecc89b2226b5bcef89999d20296610db`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `abc9f69ae4bb93e033482b9876d12452ecc89b2226b5bcef89999d20296610db`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/custom_primitive_sffi_spec.spl
mirror: doc/06_spec/unit/compiler/custom_primitive_sffi_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/custom_primitive_sffi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/custom_primitive_sffi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/custom_primitive_sffi_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/custom_primitive_sffi_spec.spl:376:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps u32 wrapper metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/custom_primitive_sffi_spec.spl:386:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps i64 wrapper metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/custom_primitive_sffi_spec.spl:394:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps bool wrapper as non-integer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
