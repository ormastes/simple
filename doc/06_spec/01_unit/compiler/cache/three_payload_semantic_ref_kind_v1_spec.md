# Three Payload Semantic Ref Kind V1 Specification

Cycle-3 canonical manual refresh: the executable spec now has 12 scenarios.
The digest fixtures use distinct valid 64-hex digests (`d("c")`, `d("d")`,
and `d("e")`); no invalid digest strings are used. This manual is aligned
without a second runner execution; compiled re-generation remains pending.

> Tests covering:

## Scenarios

### Three-payload semantic reference kind/tag contract admission

#### should preserve tags one through five and assign six and seven

- Encode and decode every semantic reference kind
   - Expected: encoded[213] equals `tags[index]`
   - Expected: decoded.ok is true
   - Expected: decoded_name equals `kind_name(kind)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Encode and decode every semantic reference kind")
val kinds = [
    ThreePayloadSemanticRefKindV1.MacroExpansion,
    ThreePayloadSemanticRefKindV1.GenericBody,
    ThreePayloadSemanticRefKindV1.TraitDefaultBody,
    ThreePayloadSemanticRefKindV1.TraitCallable,
    ThreePayloadSemanticRefKindV1.AspectCallable,
    ThreePayloadSemanticRefKindV1.ConcreteFunction,
    ThreePayloadSemanticRefKindV1.CtfeBody]
val tags = [1, 2, 3, 4, 5, 6, 7]
var index: i64 = 0
while index < kinds.len():
    val kind = kinds[index]
    val embedded = if index < 3 or index >= 5:
        # Section identity is independent of semantic-kind tag.  Keep
        # the fixture within the seal's two-section bound so a future
        # failure isolates kind/tag handling rather than bounds.
        Some(section(0, d("c")))
    else:
        nil
    val encoded = three_payload_closure_seal_encode_v2(
        seal([v2_ref(kind, "entity." + index.to_string(), embedded)]))
    expect(encoded.len()).to_be_greater_than(0)
    # With one ref and no prior digest, the frozen TPV2 layout puts the
    # first semantic-kind discriminant at byte 213.
    expect(encoded[213]).to_equal(tags[index])
    val decoded = three_payload_closure_seal_decode_v2(encoded)
    expect(decoded.ok).to_equal(true)
    val decoded_name = match decoded.value:
        case Some(value): kind_name(value.semantic_refs[0].kind)
        case nil: "missing"
    expect(decoded_name).to_equal(kind_name(kind))
    index = index + 1
```

</details>

#### should independently encode and decode a ConcreteFunction embedded body

- ConcreteFunction tag, embedded section, and decoded kind are retained.

```simple
val reference = v2_ref(ThreePayloadSemanticRefKindV1.ConcreteFunction,
    "fn.concrete", Some(section(0, d("c"))))
val encoded = three_payload_closure_seal_encode_v2(seal([reference]))
expect(encoded.len()).to_be_greater_than(0)
val decoded = three_payload_closure_seal_decode_v2(encoded)
expect(decoded.ok).to_equal(true)
expect(decoded.value.unwrap().semantic_refs[0].kind).to_equal(
    ThreePayloadSemanticRefKindV1.ConcreteFunction)
```

#### should independently encode and decode a CtfeBody embedded body

- CtfeBody tag, embedded section, and decoded kind are retained.

```simple
val reference = v2_ref(ThreePayloadSemanticRefKindV1.CtfeBody,
    "body.ctfe", Some(section(1, d("c"))))
val encoded = three_payload_closure_seal_encode_v2(seal([reference]))
expect(encoded.len()).to_be_greater_than(0)
val decoded = three_payload_closure_seal_decode_v2(encoded)
expect(decoded.ok).to_equal(true)
expect(decoded.value.unwrap().semantic_refs[0].kind).to_equal(
    ThreePayloadSemanticRefKindV1.CtfeBody)
```

#### should reject hostile unknown tags for both new kinds

- Mutated ConcreteFunction and CtfeBody tags reject with `unknown_v2_semantic_ref_kind`.

```simple
val concrete = three_payload_closure_seal_encode_v2(seal([
    v2_ref(ThreePayloadSemanticRefKindV1.ConcreteFunction,
        "fn.unknown", Some(section(0, d("c"))))]))
expect(concrete.len()).to_be_greater_than(213)
expect(three_payload_closure_seal_decode_v2(concrete).ok).to_equal(true)
var unknown = concrete.copy()
unknown[213] = 88.to_u8()
expect(three_payload_closure_seal_decode_v2(unknown).error).to_equal(
    "unknown_v2_semantic_ref_kind")
```

#### should reject hostile bounds and embedded digest mutations

- Out-of-range section index, decoded-byte budget overflow, and valid-but-wrong
  embedded digest are rejected.

```simple
expect(three_payload_semantic_ref_valid_v2(
    v2_ref(ConcreteFunction, "fn.oob", Some(section(1, d("c")))), 1, 16)).to_equal(false)
expect(three_payload_semantic_ref_valid_v2(
    v2_ref(CtfeBody, "ctfe.digest", Some(section(1, d("e")))), 2, 32)).to_equal(false)
```

#### should provide stable digest evidence and change it after a body mutation

- Canonical seal digests are 64 hexadecimal characters and differ after a
  valid body digest mutation.

```simple
val original = seal([v2_ref(ConcreteFunction, "fn.digest", Some(section(0, d("c"))))])
val changed = seal([v2_ref_with_digest(ConcreteFunction, "fn.digest", d("d"),
    Some(section(0, d("d"))))])
expect(three_payload_closure_seal_digest_v2(original).len()).to_equal(64)
expect(three_payload_closure_seal_digest_v2(changed) ==
    three_payload_closure_seal_digest_v2(original)).to_equal(false)
```

#### should reject full CtfeBody hostile bounds and digest mutations

```simple
expect(three_payload_semantic_ref_valid_v2(
    v2_ref(CtfeBody, "ctfe.oob", Some(section(2, d("c")))), 2, 16)).to_equal(false)
val large = TldSectionRefV1(role: TldPayloadRoleV1.PackageInitTld,
    section_index: 1, kind: "semantic-body", semantic_object_digest: d("c"),
    offset: 16, stored_bytes: 16, decoded_bytes: 33, encoding_profile: "raw-v1")
expect(three_payload_semantic_ref_valid_v2(
    v2_ref(CtfeBody, "ctfe.large", Some(large)), 2, 32)).to_equal(false)
expect(three_payload_semantic_ref_valid_v2(
    v2_ref(CtfeBody, "ctfe.digest", Some(section(1, d("e")))), 2, 32)).to_equal(false)
```

#### should reject missing and negative V1 embedded indices for both new kinds

```simple
var concrete_missing = v1_embedded(ConcreteFunction, "fn.missing")
concrete_missing.embedded_section_index = nil
expect(three_payload_semantic_ref_valid_v1(concrete_missing)).to_equal(false)
var ctfe_negative = v1_embedded(CtfeBody, "ctfe.negative")
ctfe_negative.embedded_section_index = Some(-1)
expect(three_payload_semantic_ref_valid_v1(ctfe_negative)).to_equal(false)
```

#### should require embedded TLD sections for concrete functions and CTFE bodies

- Validate portable body references through the V2 admission validator


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate portable body references through the V2 admission validator")
val concrete = ThreePayloadSemanticRefKindV1.ConcreteFunction
val ctfe = ThreePayloadSemanticRefKindV1.CtfeBody
expect(three_payload_semantic_ref_valid_v2(
    v2_ref(concrete, "fn.body", Some(section(0, d("c")))), 2, 32)).to_equal(true)
expect(three_payload_semantic_ref_valid_v2(
    v2_ref(ctfe, "ctfe.body", Some(section(1, d("c")))), 2, 32)).to_equal(true)
expect(three_payload_semantic_ref_valid_v2(
    v2_ref(concrete, "fn.symbolic", nil), 2, 32)).to_equal(false)
expect(three_payload_semantic_ref_valid_v2(
    v2_ref(ctfe, "ctfe.symbolic", nil), 2, 32)).to_equal(false)
expect(three_payload_semantic_ref_valid_v1(
    v1_embedded(concrete, "fn.body"))).to_equal(true)
expect(three_payload_semantic_ref_valid_v1(
    v1_embedded(ctfe, "ctfe.body"))).to_equal(true)
expect(three_payload_semantic_ref_valid_v1(
    v1_symbolic(concrete, "fn.symbolic"))).to_equal(false)
expect(three_payload_semantic_ref_valid_v1(
    v1_symbolic(ctfe, "ctfe.symbolic"))).to_equal(false)
```

</details>

#### should keep trait and aspect calls symbolic-only

- Preserve the existing symbolic trait and aspect contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Preserve the existing symbolic trait and aspect contract")
val trait = ThreePayloadSemanticRefKindV1.TraitCallable
val aspect = ThreePayloadSemanticRefKindV1.AspectCallable
expect(three_payload_semantic_ref_valid_v2(
    v2_ref(trait, "Trait.call", nil), 2, 32)).to_equal(true)
expect(three_payload_semantic_ref_valid_v2(
    v2_ref(aspect, "Aspect.before", nil), 2, 32)).to_equal(true)
expect(three_payload_semantic_ref_valid_v2(
    v2_ref(trait, "Trait.body", Some(section(0, d("c")))), 2, 32)).to_equal(false)
expect(three_payload_semantic_ref_valid_v2(
    v2_ref(aspect, "Aspect.body", Some(section(0, d("c")))), 2, 32)).to_equal(false)
expect(three_payload_semantic_ref_valid_v1(
    v1_symbolic(trait, "Trait.call"))).to_equal(true)
expect(three_payload_semantic_ref_valid_v1(
    v1_symbolic(aspect, "Aspect.before"))).to_equal(true)
expect(three_payload_semantic_ref_valid_v1(
    v1_embedded(trait, "Trait.body"))).to_equal(false)
expect(three_payload_semantic_ref_valid_v1(
    v1_embedded(aspect, "Aspect.body"))).to_equal(false)
```

</details>

#### should reject an unknown semantic kind tag instead of defaulting

- Corrupt the first semantic-kind discriminant
   - Expected: three_payload_closure_seal_decode_v2(encoded).ok is true
   - Expected: decoded.ok is false
   - Expected: decoded.error equals `unknown_v2_semantic_ref_kind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Corrupt the first semantic-kind discriminant")
val encoded = three_payload_closure_seal_encode_v2(seal([
    v2_ref(ThreePayloadSemanticRefKindV1.ConcreteFunction,
        "fn.body", Some(section(0, d("c"))))]))
expect(encoded.len()).to_be_greater_than(213)
expect(three_payload_closure_seal_decode_v2(encoded).ok).to_equal(true)
var unknown = encoded.copy()
unknown[213] = 99.to_u8()
val decoded = three_payload_closure_seal_decode_v2(unknown)
expect(decoded.ok).to_equal(false)
expect(decoded.error).to_equal("unknown_v2_semantic_ref_kind")
```

</details>

#### should admit concrete and CTFE bodies without changing worker IO rules

- Run V1 worker admission with both new embedded body kinds
   - Expected: admission equals `admitted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run V1 worker admission with both new embedded body kinds")
val refs = [v1_embedded(ThreePayloadSemanticRefKindV1.ConcreteFunction,
    "fn.body"), v1_embedded(ThreePayloadSemanticRefKindV1.CtfeBody,
    "ctfe.body"), v1_symbolic(ThreePayloadSemanticRefKindV1.TraitCallable,
    "Trait.call"), v1_symbolic(ThreePayloadSemanticRefKindV1.AspectCallable,
    "Aspect.before")]
val admission = match three_payload_worker_admit_v1(v1_seal(refs), reads()):
    case Ok(_): "admitted"
    case Err(_): "rejected"
expect(admission).to_equal("admitted")
```

</details>

#### should reject external summaries, exceptional bodies, RR, and wrong cardinality

- Exercise the worker admission-only IO and cardinality contract
   - Expected: worker_error(refs, imported) equals `external_payload`
   - Expected: worker_error(refs, exceptional) equals `external_payload`
   - Expected: worker_error(refs, rr) equals `rr_is_coordinator_only`
   - Expected: worker_error(refs, wrong_source) equals `payload_cardinality`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise the worker admission-only IO and cardinality contract")
val refs: [ThreePayloadSemanticRefV1] = []
var imported = reads()
imported.imported_summary_reads = 1
expect(worker_error(refs, imported)).to_equal("external_payload")
var exceptional = reads()
exceptional.exceptional_body_reads = 1
expect(worker_error(refs, exceptional)).to_equal("external_payload")
var rr = reads()
rr.rr_reads = 1
expect(worker_error(refs, rr)).to_equal("rr_is_coordinator_only")
var wrong_source = reads()
wrong_source.source_payload_reads = 0
expect(worker_error(refs, wrong_source)).to_equal("payload_cardinality")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Requirements | REQ-CSM-027 |
| Source | `test/01_unit/compiler/cache/three_payload_semantic_ref_kind_v1_spec.spl` |
| Updated | 2026-09-09 |
| Generator | Cycle-2 aligned manual; docgen rerun pending |

## Overview

Tests covering:
- Three-payload semantic reference kind/tag contract admission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-CSM-027](../../../../02_requirements/feature/compiler_semantic_cache_daemon_virtual_summary.md#physical-metadata-portable-objects-and-callable-aspects)


<!-- sdn-diagram:id=three_payload_semantic_ref_kind_v1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=three_payload_semantic_ref_kind_v1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

three_payload_semantic_ref_kind_v1_spec -> std
three_payload_semantic_ref_kind_v1_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=three_payload_semantic_ref_kind_v1_spec.arch hash=sha256:auto
+----------+      +-----------------------------------------+
| compiler | ---> | std                                     |
+----------+      +-----------------------------------------+
                  +-----------------------------------------+
                  | three_payload_semantic_ref_kind_v1_spec |
                  +-----------------------------------------+
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |
