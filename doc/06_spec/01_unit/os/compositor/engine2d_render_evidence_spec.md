# SimpleOS Engine2D Render Evidence

> Verifies the engine2d render evidence behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Engine2D Render Evidence

Verifies the engine2d render evidence behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-016 REQ-017 REQ-018 |
| Category | SimpleOS rendering evidence |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/simple_2d_renderdoc_backend_equivalence.md |
| Plan | doc/03_plan/sys_test/simple_2d_renderdoc_backend_equivalence.md |
| Design | doc/05_design/simple_2d_renderdoc_backend_equivalence.md |
| Research | doc/01_research/local/simple_2d_renderdoc_backend_equivalence.md |
| Source | `test/01_unit/os/compositor/engine2d_render_evidence_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the engine2d render evidence behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SimpleOS Engine2D render evidence

#### hashes stable full-alpha ARGB bytes and builds a validated receipt

- Verify: hashes stable full-alpha ARGB bytes and builds a validated receipt
- Encode two packed pixels in canonical A R G B order
   - Expected: simpleos_argb_canonical_bytes(pixels) equals `[`
- Bind the digest to one presented scanout
   - Expected: receipt == nil is false
   - Expected: proven.header.stride equals `8u32`
   - Expected: proven.event.resource_id equals `7u64`
   - Expected: proven.trailer.nonblank_pixel_count equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-016 REQ-018
step("Verify: hashes stable full-alpha ARGB bytes and builds a validated receipt")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Encode two packed pixels in canonical A R G B order")
val pixels = [0xff112233u32, 0xffaabbccu32]
expect(simpleos_argb_canonical_bytes(pixels)).to_equal([
    0xffu8, 0x11u8, 0x22u8, 0x33u8,
    0xffu8, 0xaau8, 0xbbu8, 0xccu8])
expect(simpleos_argb_pixel_sha256(pixels)).to_equal(
    "408a91f201b14cf99594b23cad79cc98a706bd120a5b2454863aac797f5d9c79")

step("Bind the digest to one presented scanout")
val receipt = simpleos_render_receipt(
    SIMPLEOS_RENDER_ARCH_X86_64,
    SIMPLEOS_RENDER_BACKEND_VIRTIO_GPU,
    FirmwareSha256(
        word0: 1u64, word1: 2u64, word2: 3u64, word3: 4u64),
    5u64, 6u64, 7u64, 2u32, 1u32, pixels)
expect(receipt == nil).to_equal(false)
val proven = receipt!
expect(proven.header.stride).to_equal(8u32)
expect(proven.event.resource_id).to_equal(7u64)
expect(proven.trailer.nonblank_pixel_count).to_equal(2u64)
```

</details>

#### keeps guest control bytes identical to the host correlation line

- Verify: keeps guest control bytes identical to the host correlation line
- Compare the no-allocation guest wire with hosted formatting


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-016 REQ-017 REQ-018
step("Verify: keeps guest control bytes identical to the host correlation line")
step("Compare the no-allocation guest wire with hosted formatting")
expect(guest_control_line(87u8, 5u64, 6u64)).to_equal(
    backend_render_capture_control_line("W", 5u64, 6u64) + "\n")
expect(guest_control_line(65u8, 5u64, 6u64)).to_equal(
    backend_render_capture_control_line("A", 5u64, 6u64) + "\n")
expect(guest_control_line(75u8, 5u64, 6u64)).to_equal(
    backend_render_capture_control_line("K", 5u64, 6u64) + "\n")
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


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_2d_renderdoc_backend_equivalence.md`
- **Plan:** `doc/03_plan/sys_test/simple_2d_renderdoc_backend_equivalence.md`
- **Design:** `doc/05_design/simple_2d_renderdoc_backend_equivalence.md`
- **Research:** `doc/01_research/local/simple_2d_renderdoc_backend_equivalence.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0766d433cc003a9266d640b85ef36c75d9ecc9f8c1a98524a543b7f625f4a365`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0766d433cc003a9266d640b85ef36c75d9ecc9f8c1a98524a543b7f625f4a365`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0766d433cc003a9266d640b85ef36c75d9ecc9f8c1a98524a543b7f625f4a365`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/compositor/engine2d_render_evidence_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/engine2d_render_evidence_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/engine2d_render_evidence_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/compositor/engine2d_render_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/engine2d_render_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
