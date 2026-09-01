# arena_as_blob_backend_spec

> Arena Core Conformance Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# arena_as_blob_backend_spec

Arena Core Conformance Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/dbfs/arena_as_blob_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Arena Core Conformance Specification

Verifies the live NVFS arena core helpers still provide the blob-backend verbs
used by the hosted DBFS/NVFS path:
  - create / append / read / seal / discard / clone_range / preferred_granule

## Scenarios

### Arena core conformance

#### general-mutable arena passes full conformance suite

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- general-mutable arena passes full conformance suite


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("general-mutable arena passes full conformance suite")
run_conformance_suite(0)
```

</details>

#### clone_range copies data correctly

- clone_range copies data correctly
   - Expected: arena_append_impl(src, payload, 0) equals `2`
   - Expected: arena_clone_range_impl(src, 0, dst, 0, 2) equals `2`
   - Expected: out[0] equals `0xAB`
   - Expected: out[1] equals `0xCD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clone_range copies data correctly")
val src = arena_create_impl(0, 4096)
val payload: [u8] = [0xAB, 0xCD]
expect(arena_append_impl(src, payload, 0)).to_equal(2)
val dst = arena_create_impl(0, 4096)
expect(arena_clone_range_impl(src, 0, dst, 0, 2)).to_equal(2)
val out = arena_readv_impl(dst, 0, 2)
expect(out[0]).to_equal(0xAB)
expect(out[1]).to_equal(0xCD)
```

</details>

#### preferred_granule is at least 512

- preferred_granule is at least 512
   - Expected: arena_preferred_granule_impl(h) >= 512 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preferred_granule is at least 512")
val h = arena_create_impl(0, 4096)
expect(arena_preferred_granule_impl(h) >= 512).to_equal(true)
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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dd0db5d40d53f91f344866f58c3d6befa31be74a86d03c851ee1a2be77da4b2a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dd0db5d40d53f91f344866f58c3d6befa31be74a86d03c851ee1a2be77da4b2a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dd0db5d40d53f91f344866f58c3d6befa31be74a86d03c851ee1a2be77da4b2a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/storage/dbfs/arena_as_blob_backend_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/arena_as_blob_backend_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/arena_as_blob_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/arena_as_blob_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/arena_as_blob_backend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/storage/dbfs/arena_as_blob_backend_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'general-mutable arena passes full conformance suite' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/arena_as_blob_backend_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clone_range copies data correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/arena_as_blob_backend_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preferred_granule is at least 512' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
