# Model Loader Tensor Bytes Specification

> Tests covering Slang tensor byte range loader.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Model Loader Tensor Bytes Specification

## Scenarios

### Slang tensor byte range loader

#### loads the declared tensor byte range from a validated pack

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads the declared tensor byte range from a validated pack
   - Expected: tensor_byte_status(root, name) equals `ok`
   - Expected: tensor_byte_len(root, name) equals `16`
   - Expected: tensor_byte_at(root, name, 0) equals `48`
   - Expected: tensor_byte_at(root, name, 15) equals `102`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads the declared tensor byte range from a validated pack")
val root = "test/fixtures/slang/valid_pack"
val name = "tok_embeddings.weight"
expect(tensor_byte_status(root, name)).to_equal("ok")
expect(tensor_byte_len(root, name)).to_equal(16)
expect(tensor_byte_at(root, name, 0)).to_equal(48)
expect(tensor_byte_at(root, name, 15)).to_equal(102)
```

</details>

#### loads a declared tensor byte range spanning sequential chunks

- loads a declared tensor byte range spanning sequential chunks
   - Expected: tensor_byte_status(root, name) equals `ok`
   - Expected: tensor_byte_len(root, name) equals `7`
   - Expected: tensor_byte_at(root, name, 0) equals `98`
   - Expected: tensor_byte_at(root, name, 3) equals `10`
   - Expected: tensor_byte_at(root, name, 4) equals `69`
   - Expected: tensor_byte_at(root, name, 6) equals `71`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads a declared tensor byte range spanning sequential chunks")
val root = "test/fixtures/slang/cross_chunk_pack"
val name = "split.weight"
expect(tensor_byte_status(root, name)).to_equal("ok")
expect(tensor_byte_len(root, name)).to_equal(7)
expect(tensor_byte_at(root, name, 0)).to_equal(98)
expect(tensor_byte_at(root, name, 3)).to_equal(10)
expect(tensor_byte_at(root, name, 4)).to_equal(69)
expect(tensor_byte_at(root, name, 6)).to_equal(71)
```

</details>

#### reports missing tensor names explicitly

- reports missing tensor names explicitly
   - Expected: tensor_byte_status("test/fixtures/slang/valid_pack", "missing.weight") equals `tensor_not_found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports missing tensor names explicitly")
expect(tensor_byte_status("test/fixtures/slang/valid_pack", "missing.weight")).to_equal("tensor_not_found")
```

</details>

#### does not read bytes from invalid packs

- does not read bytes from invalid packs
   - Expected: tensor_byte_status("test/fixtures/slang/missing_chunk_pack", "tok_embeddings.weight") equals `chunk_error`
   - Expected: tensor_byte_status("test/fixtures/slang/wrong_chunk_pack", "tok_embeddings.weight") equals `chunk_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not read bytes from invalid packs")
expect(tensor_byte_status("test/fixtures/slang/missing_chunk_pack", "tok_embeddings.weight")).to_equal("chunk_error")
expect(tensor_byte_status("test/fixtures/slang/wrong_chunk_pack", "tok_embeddings.weight")).to_equal("chunk_error")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/slang/model_loader_tensor_bytes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Slang tensor byte range loader.
- Slang tensor byte range loader

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

- Canonical SPipe generation for source `e408d0b05aa67c303248a5a722e5a3bd50988992dd28dbb8026d13a368283a9e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e408d0b05aa67c303248a5a722e5a3bd50988992dd28dbb8026d13a368283a9e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e408d0b05aa67c303248a5a722e5a3bd50988992dd28dbb8026d13a368283a9e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/gc_async_mut/slang/model_loader_tensor_bytes_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/slang/model_loader_tensor_bytes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/slang/model_loader_tensor_bytes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/slang/model_loader_tensor_bytes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/slang/model_loader_tensor_bytes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/slang/model_loader_tensor_bytes_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads the declared tensor byte range from a validated pack' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/slang/model_loader_tensor_bytes_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads a declared tensor byte range spanning sequential chunks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/slang/model_loader_tensor_bytes_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports missing tensor names explicitly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
