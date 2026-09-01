# Scv Wasm Shim Contract Specification

> Tests covering scv hardened WASM shim contract (SCV-IMPL-P-02).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Wasm Shim Contract Specification

## Scenarios

### scv hardened WASM shim contract (SCV-IMPL-P-02)

#### memory/fuel bounds constants are positive and sane

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- memory/fuel bounds constants are positive and sane
   - Expected: scv_wasm_max_input_bytes() equals `16777216`
   - Expected: scv_wasm_fuel_budget() equals `1000000000`
   - Expected: scv_wasm_max_memory_pages() > 0 is true
   - Expected: scv_wasm_max_node_depth() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("memory/fuel bounds constants are positive and sane")
expect(scv_wasm_max_input_bytes()).to_equal(16777216)
expect(scv_wasm_fuel_budget()).to_equal(1000000000)
expect(scv_wasm_max_memory_pages() > 0).to_equal(true)
expect(scv_wasm_max_node_depth() > 0).to_equal(true)
```

</details>

#### input bounds: zero and max accepted, negative and oversized refused

- input bounds: zero and max accepted, negative and oversized refused
   - Expected: scv_wasm_input_within_bounds(0) is true
   - Expected: scv_wasm_input_within_bounds(scv_wasm_max_input_bytes()) is true
   - Expected: scv_wasm_input_within_bounds(scv_wasm_max_input_bytes() + 1) is false
   - Expected: scv_wasm_input_within_bounds(-1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("input bounds: zero and max accepted, negative and oversized refused")
expect(scv_wasm_input_within_bounds(0)).to_equal(true)
expect(scv_wasm_input_within_bounds(scv_wasm_max_input_bytes())).to_equal(true)
expect(scv_wasm_input_within_bounds(scv_wasm_max_input_bytes() + 1)).to_equal(false)
expect(scv_wasm_input_within_bounds(-1)).to_equal(false)
```

</details>

#### ABI check: supported range inclusive, outside refused

- ABI check: supported range inclusive, outside refused
   - Expected: scv_wasm_abi_supported(scv_wasm_abi_min()) is true
   - Expected: scv_wasm_abi_supported(scv_wasm_abi_max()) is true
   - Expected: scv_wasm_abi_supported(scv_wasm_abi_min() - 1) is false
   - Expected: scv_wasm_abi_supported(scv_wasm_abi_max() + 1) is false
   - Expected: scv_wasm_abi_supported(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ABI check: supported range inclusive, outside refused")
expect(scv_wasm_abi_supported(scv_wasm_abi_min())).to_equal(true)
expect(scv_wasm_abi_supported(scv_wasm_abi_max())).to_equal(true)
expect(scv_wasm_abi_supported(scv_wasm_abi_min() - 1)).to_equal(false)
expect(scv_wasm_abi_supported(scv_wasm_abi_max() + 1)).to_equal(false)
expect(scv_wasm_abi_supported(0)).to_equal(false)
```

</details>

#### signature verification: exact locked sha256 match only, empty never passes

- signature verification: exact locked sha256 match only, empty never passes
   - Expected: scv_wasm_grammar_signature_ok(h, h) is true
   - Expected: scv_wasm_grammar_signature_ok(h, "sha256_def456") is false
   - Expected: scv_wasm_grammar_signature_ok("", h) is false
   - Expected: scv_wasm_grammar_signature_ok(h, "") is false
   - Expected: scv_wasm_grammar_signature_ok("md5_abc", "md5_abc") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("signature verification: exact locked sha256 match only, empty never passes")
val h = "sha256_abc123"
expect(scv_wasm_grammar_signature_ok(h, h)).to_equal(true)
expect(scv_wasm_grammar_signature_ok(h, "sha256_def456")).to_equal(false)
expect(scv_wasm_grammar_signature_ok("", h)).to_equal(false)
expect(scv_wasm_grammar_signature_ok(h, "")).to_equal(false)
expect(scv_wasm_grammar_signature_ok("md5_abc", "md5_abc")).to_equal(false)
```

</details>

#### well-formed blob validates clean

- well-formed blob validates clean
   - Expected: scv_wasm_blob_validate(blob, 11) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("well-formed blob validates clean")
val blob = "file|root|0|11|0|0\nline||0|5|1|1\nline||6|11|1|1\n"
expect(scv_wasm_blob_validate(blob, 11)).to_equal("")
```

</details>

#### fuzz corpus: every malformed blob is rejected with a reason

- fuzz corpus: every malformed blob is rejected with a reason
   - Expected: verdict == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fuzz corpus: every malformed blob is rejected with a reason")
# (blob, expected reason substring) — pinned corpus of shim-output
# corruptions seen or anticipated; a malformed blob must NEVER
# validate clean and turn into a half-built tree.
val corpus = [
    ("", "empty_blob"),
    ("\n\n", "empty_blob"),
    ("file|root|0|5|0\n", "field_count"),
    ("file|root|0|5|0|0|extra\nonly|four|fields|here\n", "field_count"),
    ("|root|0|5|0|0\n", "empty_kind"),
    ("file|root|-1|5|0|0\n", "negative_offset"),
    ("file|root|0|-5|0|0\n", "negative_offset"),
    ("file|root|9|5|0|0\n", "end_before_start"),
    ("file|root|0|999|0|0\n", "out_of_bounds"),
    ("file|root|0|5|2|0\n", "bad_leaf_flag"),
    ("file|root|0|5|x|0\n", "bad_leaf_flag"),
    ("file|root|0|5|0|-1\n", "negative_depth"),
    ("file|root|0|5|0|1\n", "root_not_depth_zero"),
    ("file|root|0|5|0|0\nline||0|5|1|2\n", "depth_jump"),
    ("file|root|0|5|0|0\nfile|root|0|5|0|0\n", "multiple_roots"),
    ("file|root|0|5|0|0\nline||0|5|1|9999\n", "depth_overflow"),
]
var i = 0
while i < corpus.len():
    val (blob, reason) = corpus[i]
    val verdict = scv_wasm_blob_validate(blob, 10)
    expect(verdict == "").to_equal(false)
    expect(verdict).to_contain(reason)
    i = i + 1
```

</details>

#### deterministic serialization: normalize is idempotent and canonical blobs are fixpoints

- deterministic serialization: normalize is idempotent and canonical blobs are fixpoints
   - Expected: once equals `twice`
   - Expected: once equals `blob`
   - Expected: scv_wasm_blob_normalize(noisy) equals `blob`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("deterministic serialization: normalize is idempotent and canonical blobs are fixpoints")
val blob = "file|root|0|11|0|0\nline||0|5|1|1\nline||6|11|1|1\n"
val once = scv_wasm_blob_normalize(blob)
val twice = scv_wasm_blob_normalize(once)
expect(once).to_equal(twice)
expect(once).to_equal(blob)
# blank-line noise normalizes away deterministically
val noisy = "file|root|0|11|0|0\n\nline||0|5|1|1\n\n\nline||6|11|1|1\n"
expect(scv_wasm_blob_normalize(noisy)).to_equal(blob)
```

</details>

#### blob digest is deterministic and content-sensitive

- blob digest is deterministic and content-sensitive
   - Expected: scv_wasm_blob_digest(a) equals `scv_wasm_blob_digest(a)`
   - Expected: scv_wasm_blob_digest(a) == scv_wasm_blob_digest(b) is false
   - Expected: scv_wasm_blob_digest(a).starts_with("wasm_blob_") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("blob digest is deterministic and content-sensitive")
val a = "file|root|0|11|0|0\nline||0|5|1|1\n"
val b = "file|root|0|11|0|0\nline||0|6|1|1\n"
expect(scv_wasm_blob_digest(a)).to_equal(scv_wasm_blob_digest(a))
expect(scv_wasm_blob_digest(a) == scv_wasm_blob_digest(b)).to_equal(false)
expect(scv_wasm_blob_digest(a).starts_with("wasm_blob_")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/integration/runtime/scv_wasm_shim_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv hardened WASM shim contract (SCV-IMPL-P-02).
- scv hardened WASM shim contract (SCV-IMPL-P-02)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fa9cb0512259489fceb620c71cd8f068c76456ead94d8dd3e0e419ed01e36076`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fa9cb0512259489fceb620c71cd8f068c76456ead94d8dd3e0e419ed01e36076`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fa9cb0512259489fceb620c71cd8f068c76456ead94d8dd3e0e419ed01e36076`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/runtime/scv_wasm_shim_contract_spec.spl
mirror: doc/06_spec/integration/runtime/scv_wasm_shim_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/runtime/scv_wasm_shim_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/runtime/scv_wasm_shim_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/runtime/scv_wasm_shim_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/runtime/scv_wasm_shim_contract_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'memory/fuel bounds constants are positive and sane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/runtime/scv_wasm_shim_contract_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'input bounds: zero and max accepted, negative and oversized refused' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/runtime/scv_wasm_shim_contract_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ABI check: supported range inclusive, outside refused' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
