# dict_get_struct_value_spec

> Dict<text, StructValue>.get() Returns a Corrupt Option on a Hit (Native)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dict_get_struct_value_spec

Dict<text, StructValue>.get() Returns a Corrupt Option on a Hit (Native)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/dict_get_struct_value_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Dict<text, StructValue>.get() Returns a Corrupt Option on a Hit (Native)

Bug doc: doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md
Related: doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md

Mirrors probe B/C from the bug doc: a struct-valued dict field
(`Holder.traits: Dict<text, Tr>`) with one real entry. `contains_key`, the
index read `d[k]`, and a manually-constructed `Some(d[k])` all behave
correctly on both hit and miss. `.get(k)` is correct on a MISS (nil) but on a
HIT returns a non-nil Option whose payload is corrupt -- unwrapping it and
reading a field segfaults under native codegen (isolated probe evidence in
the bug doc; this spec asserts the safe alternatives plus the desired -- not
today's -- contract for the hit case).

EXPECTED RED (one scenario only): "get() on a hit yields a usable value" is
deliberately red under native codegen until the `.get()` lowering is fixed to
decode identically to `d[k]` (see bug doc "Suggested fix"). Per repo
convention for filed defects (precedent: nil_dict_receiver_phantom_option_spec.spl,
rv32_trap_completeness_spec.spl), it must stay visibly red -- do NOT skip()
it. All other scenarios in this file pin behavior that is already correct
today and must stay green.

## Scenarios

### Dict<text, StructValue> contains_key and index read (correct today)

#### contains_key reports true on a hit and false on a miss

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- contains_key reports true on a hit and false on a miss
   - Expected: h.traits.contains_key("Read") is true
   - Expected: h.traits.contains_key("Nope") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("contains_key reports true on a hit and false on a miss")
val h = make_holder()
expect(h.traits.contains_key("Read")).to_equal(true)
expect(h.traits.contains_key("Nope")).to_equal(false)
```

</details>

#### index read on a hit returns a usable struct with correct fields

- index read on a hit returns a usable struct with correct fields
   - Expected: idx.name equals `Read`
   - Expected: idx.n equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("index read on a hit returns a usable struct with correct fields")
val h = make_holder()
val idx = h.traits["Read"]
expect(idx.name).to_equal("Read")
expect(idx.n).to_equal(5)
```

</details>

### Some(index_read) manual wrap round-trips correctly (safe alternative)

#### Some(d[k]) is non-nil and unwraps to the correct struct

- Some(d[k]) is non-nil and unwraps to the correct struct
   - Expected: o == nil is false
   - Expected: o.unwrap().name equals `Read`
   - Expected: o.unwrap().n equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Some(d[k]) is non-nil and unwraps to the correct struct")
val h = make_holder()
val v = h.traits["Read"]
val o: Tr? = Some(v)
expect(o == nil).to_equal(false)
expect(o.unwrap().name).to_equal("Read")
expect(o.unwrap().n).to_equal(5)
```

</details>

#### a nil Tr? stays nil through the same shape

- a nil Tr? stays nil through the same shape
   - Expected: n == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a nil Tr? stays nil through the same shape")
val n: Tr? = nil
expect(n == nil).to_equal(true)
```

</details>

### Dict<text, StructValue>.get() (native corrupt-Option bug)

#### get() on a miss is correctly nil

- get() on a miss is correctly nil
   - Expected: miss == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("get() on a miss is correctly nil")
val h = make_holder()
val miss = h.traits.get("Nope")
expect(miss == nil).to_equal(true)
```

</details>

#### get() on a hit yields a usable value

- get() on a hit yields a usable value
   - Expected: hit == nil is false
   - Expected: hit.unwrap().name equals `Read`
   - Expected: hit.unwrap().n equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("get() on a hit yields a usable value")
# DELIBERATE RED under native codegen (bug
# native_dict_get_struct_value_corrupt_option_2026-07-27.md, Probe B):
# h.traits.get("Read") returns a non-nil Option, but the payload is
# corrupt -- .unwrap().name segfaults on the native binary today.
# Do NOT skip() this scenario; it stays red until the .get() MIR
# lowering decodes struct-valued dict results identically to the
# d[k] index-read path (see bug doc "Suggested fix").
val h = make_holder()
val hit = h.traits.get("Read")
expect(hit == nil).to_equal(false)
expect(hit.unwrap().name).to_equal("Read")
expect(hit.unwrap().n).to_equal(5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `4cef26882dee46fa7b5b653e61c17ad780358f6da5df78a8f03611cd57bb55ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4cef26882dee46fa7b5b653e61c17ad780358f6da5df78a8f03611cd57bb55ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4cef26882dee46fa7b5b653e61c17ad780358f6da5df78a8f03611cd57bb55ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/native/dict_get_struct_value_spec.spl
mirror: doc/06_spec/01_unit/compiler/native/dict_get_struct_value_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/native/dict_get_struct_value_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/native/dict_get_struct_value_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/native/dict_get_struct_value_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/native/dict_get_struct_value_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains_key reports true on a hit and false on a miss' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/dict_get_struct_value_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'index read on a hit returns a usable struct with correct fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/dict_get_struct_value_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Some(d[k]) is non-nil and unwraps to the correct struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
