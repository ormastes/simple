# struct_dict_field_map_copy_spec

> Struct-Field Map Copy — Nested Dicts Must Survive (Native Regression)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# struct_dict_field_map_copy_spec

Struct-Field Map Copy — Nested Dicts Must Survive (Native Regression)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/struct_dict_field_map_copy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Struct-Field Map Copy — Nested Dicts Must Survive (Native Regression)

Bug doc: doc/08_tracking/bug/native_struct_field_map_copy_nilfills_nested_dicts_2026-07-27.md

Lineage: a struct field of type `Dict<text, StructValue>` where `StructValue`
itself holds a `Dict` (and an array) field. Populating a standalone map with
one entry, then assigning that map into the struct field (`Holder(by_name:
populated_map)`), and reading the entry back out of the struct-field copy
should reproduce the same struct value the standalone map held. Under native
codegen the struct-field copy is suspected to nil-fill (or otherwise corrupt)
the nested `Dict`/array fields of the copied struct value, even though reading
directly from the original (uncopied) map is fine — the classic "seed
NIL-FILLS omitted struct-init fields" defect family, but here triggered by a
map-value copy through a struct field rather than an omitted constructor arg.

This spec pins the DESIRED contract: reading `Inner.items`/`Inner.order` back
out of `Holder.by_name.get(key)` after assigning a populated map into the
struct field must observe the same len()/contains_key()/order as the entry
held directly in the original map.

EXPECTED: PASS under interpreter mode (verified via `bin/simple test
test/01_unit/compiler/native/struct_dict_field_map_copy_spec.spl
--mode=interpreter`) — this is a native-codegen-only defect, so the
interpreter lane does not reproduce it. If the native lane reproduces the
struct-field map-copy nil-fill, the "struct-field map copy" scenario below is
deliberately RED there; per repo convention for filed defects (precedent:
nil_dict_receiver_phantom_option_spec.spl), it must stay visibly red — do NOT
skip() it.

## Scenarios

### struct-field map copy preserves nested dicts (native regression)

#### preserves nested dicts through a struct-field map copy

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves nested dicts through a struct-field map copy
   - Expected: inner.items.len() equals `2`
   - Expected: inner.items.contains_key("alpha") is true
   - Expected: inner.items.contains_key("beta") is true
   - Expected: inner.order.len() equals `2`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves nested dicts through a struct-field map copy")
val populated_map = make_populated_map()
val holder = Holder(by_name: populated_map)

if val inner = holder.by_name.get("first"):
    expect(inner.items.len()).to_equal(2)
    expect(inner.items.contains_key("alpha")).to_equal(true)
    expect(inner.items.contains_key("beta")).to_equal(true)
    expect(inner.order.len()).to_equal(2)
else:
    expect(true).to_equal(false)
```

</details>

#### preserves nested dicts when reading directly from the original map (control)

- preserves nested dicts when reading directly from the original map (control)
   - Expected: inner.items.len() equals `2`
   - Expected: inner.items.contains_key("alpha") is true
   - Expected: inner.items.contains_key("beta") is true
   - Expected: inner.order.len() equals `2`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves nested dicts when reading directly from the original map (control)")
val populated_map = make_populated_map()

if val inner = populated_map.get("first"):
    expect(inner.items.len()).to_equal(2)
    expect(inner.items.contains_key("alpha")).to_equal(true)
    expect(inner.items.contains_key("beta")).to_equal(true)
    expect(inner.order.len()).to_equal(2)
else:
    expect(true).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `eb1c69a22201d6f262d9e8754b6c5bb1ae71340bfb1947f1b7b0eb8013a9e506`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb1c69a22201d6f262d9e8754b6c5bb1ae71340bfb1947f1b7b0eb8013a9e506`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb1c69a22201d6f262d9e8754b6c5bb1ae71340bfb1947f1b7b0eb8013a9e506`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/native/struct_dict_field_map_copy_spec.spl
mirror: doc/06_spec/01_unit/compiler/native/struct_dict_field_map_copy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/native/struct_dict_field_map_copy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/native/struct_dict_field_map_copy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/native/struct_dict_field_map_copy_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/native/struct_dict_field_map_copy_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves nested dicts through a struct-field map copy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/struct_dict_field_map_copy_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves nested dicts when reading directly from the original map (control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
