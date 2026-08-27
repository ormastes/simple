# SOSIX seal-before-share draw-IR command buffer (#39 Gap #1)

> Proves the host-lane immutability primitive that turns a raw draw-IR

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SOSIX seal-before-share draw-IR command buffer (#39 Gap #1)

Proves the host-lane immutability primitive that turns a raw draw-IR

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/sealed_draw_ir_payload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the host-lane immutability primitive that turns a raw draw-IR
payload_text into an immutable command buffer before it enters the runtime GPU
queue. Mirrors SharedDataset semantics
(src/os/kernel/ipc/shared_dataset.spl): write-gate :98, one-way seal :126-133,
read-rejects-unless-sealed :160. Pure — no Metal, no bit-exact pixel path.

## Scenarios

### SOSIX seal-before-share draw-IR command buffer (#39 Gap #1)

#### starts building (unsealed) and reads empty until sealed

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts building (unsealed) and reads empty until sealed


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts building (unsealed) and reads empty until sealed")
val b = draw_ir_payload_new()
assert_false(draw_ir_payload_is_sealed(b))
# read-rejects-unless-sealed: even after a write, an unsealed buffer reads ""
val w = draw_ir_payload_write(b, "draw_rect 0 0 4 4")
assert_equal(draw_ir_payload_read(w), "")
```

</details>

#### seals a written buffer and then reads its content

- seals a written buffer and then reads its content


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("seals a written buffer and then reads its content")
val b = draw_ir_payload_new()
val w = draw_ir_payload_write(b, "draw_rect 0 0 4 4")
val s = draw_ir_payload_seal(w)
assert_true(draw_ir_payload_is_sealed(s))
assert_equal(draw_ir_payload_read(s), "draw_rect 0 0 4 4")
```

</details>

#### rejects a write after seal (immutability gate)

- rejects a write after seal (immutability gate)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a write after seal (immutability gate)")
val s = engine2d_host_gpu_seal_draw_ir_payload("cmd_a")
val attempted = draw_ir_payload_write(s, "cmd_b_injected")
# the post-seal write is rejected — content unchanged, still sealed
assert_true(draw_ir_payload_is_sealed(attempted))
assert_equal(draw_ir_payload_read(attempted), "cmd_a")
```

</details>

#### seal is one-way / idempotent (a second seal is a no-op)

- seal is one-way / idempotent (a second seal is a no-op)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("seal is one-way / idempotent (a second seal is a no-op)")
val s1 = engine2d_host_gpu_seal_draw_ir_payload("cmd")
val s2 = draw_ir_payload_seal(s1)
assert_true(draw_ir_payload_is_sealed(s2))
assert_equal(draw_ir_payload_read(s2), "cmd")
```

</details>

#### gives a stable non-zero content hash after seal, identical for identical bytes

- gives a stable non-zero content hash after seal, identical for identical bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives a stable non-zero content hash after seal, identical for identical bytes")
val a = engine2d_host_gpu_seal_draw_ir_payload("same-bytes")
val b = engine2d_host_gpu_seal_draw_ir_payload("same-bytes")
assert_true(a.payload_hash != 0)
assert_equal(a.payload_hash, b.payload_hash)
```

</details>

#### gives different hashes for different payloads

- gives different hashes for different payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives different hashes for different payloads")
val a = engine2d_host_gpu_seal_draw_ir_payload("payload-one")
val b = engine2d_host_gpu_seal_draw_ir_payload("payload-two")
assert_true(a.payload_hash != b.payload_hash)
```

</details>

#### the convenience seal builds, writes, and seals in one call

- the convenience seal builds, writes, and seals in one call


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the convenience seal builds, writes, and seals in one call")
val s = engine2d_host_gpu_seal_draw_ir_payload("draw_gradient 0 0 8 8")
assert_true(draw_ir_payload_is_sealed(s))
assert_equal(draw_ir_payload_read(s), "draw_gradient 0 0 8 8")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `88df80489f98b693c3bd07d4a7136c6eadb1f4e96258e349fbbf2895a3f4ebcb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88df80489f98b693c3bd07d4a7136c6eadb1f4e96258e349fbbf2895a3f4ebcb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88df80489f98b693c3bd07d4a7136c6eadb1f4e96258e349fbbf2895a3f4ebcb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/sealed_draw_ir_payload_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/sealed_draw_ir_payload_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/sealed_draw_ir_payload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/sealed_draw_ir_payload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/sealed_draw_ir_payload_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts building (unsealed) and reads empty until sealed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/sealed_draw_ir_payload_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'seals a written buffer and then reads its content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/sealed_draw_ir_payload_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a write after seal (immutability gate)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
