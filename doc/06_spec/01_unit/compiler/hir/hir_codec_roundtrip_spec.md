# hir_codec_roundtrip_spec

> Purpose: Prove that the generated HirModule codec reproduces a REAL lowered

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hir_codec_roundtrip_spec

Purpose: Prove that the generated HirModule codec reproduces a REAL lowered

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_codec_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose: Prove that the generated HirModule codec reproduces a REAL lowered
module: encode -> decode -> encode is byte-identical, the decoded aggregate
has the same shape (functions, structs, enums, symbols), and a foreign or
truncated blob decodes to nil rather than to a partial module.

The codec (src/compiler/20.hir/generated/hir_codec.spl) is generated from
the HIR declarations by src/app/compiler_schema/codec_gen.spl so a new
variant cannot be silently skipped; this spec is the runtime half of that
guarantee, through the real pipeline parse_full_frontend -> HirLowering.
doc/08_tracking/bug/native_build_phases_after_parse_single_threaded_2026-08-22.md

HARNESS NOTE: `use compiler.hir.hir_lowering.statements.*` is REQUIRED for
lower_module (see enum_payload_range_or_frontend_exec_spec.spl).

## Scenarios

### HirModule codec round trip

#### re-encodes a decoded real module byte-identically

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-encodes a decoded real module byte-identically
- Verify: re-encodes a decoded real module byte-identically
   - Expected: hm.functions.len() > 0 is true
   - Expected: blob != "" is true
   - Expected: blob.starts_with(hir_codec_header() + "\n") is true
   - Expected: decoded != nil is true
   - Expected: again.len() equals `blob.len()`
   - Expected: again == blob is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("re-encodes a decoded real module byte-identically")
step("Verify: re-encodes a decoded real module byte-identically")
val hm = lower(SRC)
expect(hm.functions.len() > 0).to_equal(true)
val blob = hir_module_encode(hm)
expect(blob != "").to_equal(true)
expect(blob.starts_with(hir_codec_header() + "\n")).to_equal(true)
val decoded = hir_module_decode(blob)
expect(decoded != nil).to_equal(true)
val again = hir_module_encode(decoded.unwrap())
expect(again.len()).to_equal(blob.len())
expect(again == blob).to_equal(true)
```

</details>

#### preserves the module shape: functions, structs, enums, traits, impls, symbols

- preserves the module shape: functions, structs, enums, traits, impls, symbols
- Verify: preserves the module shape
   - Expected: back.name equals `hm.name`
   - Expected: back.functions.len() equals `hm.functions.len()`
   - Expected: back.structs.len() equals `hm.structs.len()`
   - Expected: back.enums.len() equals `hm.enums.len()`
   - Expected: back.traits.len() equals `hm.traits.len()`
   - Expected: back.impls.len() equals `hm.impls.len()`
   - Expected: back.symbols.symbols.len() equals `hm.symbols.symbols.len()`
   - Expected: back.symbols.next_symbol_id equals `hm.symbols.next_symbol_id`
   - Expected: back.symbols.scopes.len() equals `hm.symbols.scopes.len()`
   - Expected: keys_b[i].id equals `keys_a[i].id`
   - Expected: back.functions[keys_b[i]].name equals `hm.functions[keys_a[i]].name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves the module shape: functions, structs, enums, traits, impls, symbols")
step("Verify: preserves the module shape")
val hm = lower(SRC)
val back = hir_module_decode(hir_module_encode(hm)).unwrap()
expect(back.name).to_equal(hm.name)
expect(back.functions.len()).to_equal(hm.functions.len())
expect(back.structs.len()).to_equal(hm.structs.len())
expect(back.enums.len()).to_equal(hm.enums.len())
expect(back.traits.len()).to_equal(hm.traits.len())
expect(back.impls.len()).to_equal(hm.impls.len())
expect(back.symbols.symbols.len()).to_equal(hm.symbols.symbols.len())
expect(back.symbols.next_symbol_id).to_equal(hm.symbols.next_symbol_id)
expect(back.symbols.scopes.len()).to_equal(hm.symbols.scopes.len())
# Dict iteration order is part of the contract (MIR walks .values()).
val keys_a = hm.functions.keys()
val keys_b = back.functions.keys()
var i = 0
while i < keys_a.len():
    expect(keys_b[i].id).to_equal(keys_a[i].id)
    expect(back.functions[keys_b[i]].name).to_equal(hm.functions[keys_a[i]].name)
    i = i + 1
```

</details>

#### rejects a foreign header and a truncated blob instead of returning a partial module

- rejects a foreign header and a truncated blob instead of returning a partial module
- Verify: rejects a foreign header and a truncated blob
   - Expected: hir_module_decode("") equals `nil`
   - Expected: hir_module_decode("spl-hircodec-v0 x\n" + blob) equals `nil`
   - Expected: hir_module_decode(cut) equals `nil`
   - Expected: hir_module_decode(blob + "7\n") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a foreign header and a truncated blob instead of returning a partial module")
step("Verify: rejects a foreign header and a truncated blob")
val hm = lower(SRC)
val blob = hir_module_encode(hm)
expect(hir_module_decode("")).to_equal(nil)
expect(hir_module_decode("spl-hircodec-v0 x\n" + blob)).to_equal(nil)
val cut = blob.substring(0, blob.len() / 2)
expect(hir_module_decode(cut)).to_equal(nil)
expect(hir_module_decode(blob + "7\n")).to_equal(nil)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1ee6764e10ea4063fc2d34a3a5514a82e8f6cd619774bacc3dc575119f75282a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1ee6764e10ea4063fc2d34a3a5514a82e8f6cd619774bacc3dc575119f75282a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1ee6764e10ea4063fc2d34a3a5514a82e8f6cd619774bacc3dc575119f75282a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/hir_codec_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_codec_roundtrip_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_codec_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_codec_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_codec_roundtrip_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-encodes a decoded real module byte-identically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_codec_roundtrip_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves the module shape: functions, structs, enums, traits, impls, symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_codec_roundtrip_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a foreign header and a truncated blob instead of returning a partial module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
