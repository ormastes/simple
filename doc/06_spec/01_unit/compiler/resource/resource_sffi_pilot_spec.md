# `resource` SFFI binding — pilot migration (intended surface, currently RED)

> This spec drives the **real** Grammar-A surface the design doc specifies —

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `resource` SFFI binding — pilot migration (intended surface, currently RED)

This spec drives the **real** Grammar-A surface the design doc specifies —

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Design | doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md |
| Source | `test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Why this whole file is expected to fail to load

This spec drives the **real** Grammar-A surface the design doc specifies —
`@sffi(prefix: "...", invalid: ...) resource X` module-level declarations —
through the same `bin/simple test` interpreter path every other spec in this
tree loads through. It does NOT hand-roll a workaround class.

As of 2026-08-07, `resource` is not a parsed declaration kind anywhere in
`src/compiler/10.frontend/**` (repo-wide grep for `parse_resource_decl` /
`DECL_RESOURCE` / `@sffi` returns zero hits outside the design docs
themselves), and the architecture doc's own §5.1 "full wire-point checklist"
lists the ~13 sites (`decl_nodes.spl`, `enum_module_body.spl`,
`c_codegen.spl`, `eval_decls.spl`, ...) a new declaration kind must touch —
none of which exist yet. This is WP-A in
`doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md`,
not landed as of this writing (confirmed: no uncommitted WP-A work in any
live sibling session's working tree either — see the bug doc).

So the module-level `resource` declarations below cannot parse. Per
`.claude/rules/testing.md`, this file MUST stay RED, not be weakened to test
a parseable substitute — a hand-rolled `class File { handle: i64 }` wrapper
would prove nothing about the actual feature and would just be more of the
exact boilerplate `resource` exists to delete (see the design doc's own
`image_sffi.spl` exemplar).

## The four pilot families (chosen for ownership-strategy diversity)

1. **File** (`src/lib/nogc_sync_mut/io/file.spl`, tier `nogc_sync_mut`) —
   unique `R`, no retain/release pair -> `sharing: none`.
2. **Image** (`src/lib/nogc_sync_mut/io/image_sffi.spl`, tier
   `nogc_sync_mut`) — unique `R`; the design doc's own named pilot exemplar.
3. **CudaPrimaryContext**
   (`src/lib/nogc_sync_mut/gpu/engine2d/cuda_session.spl`, tier
   `nogc_sync_mut`) — has a real `retain`/`release` pair
   (`rt_cuda_primary_ctx_retain` / `rt_cuda_primary_ctx_release`) ->
   `sharing: foreign`, exercises `*R` foreign-RC lowering.
4. **AtomicCounter** (`src/lib/gc_async_mut/atomic.spl`, tier `gc_async_mut`)
   — no foreign retain/release -> `sharing: wrapper` if shared at all;
   exercises a `gc_*`-tier resource where `*R` allocates a Simple-side
   control block (allowed — unlike `nogc_async_mut_noalloc`, `gc_async_mut`
   permits allocation).

Once WP-A (+ WP-H for the generated wrapper methods) lands, this file's
`describe`/`it` bodies below are the intended acceptance surface: double
`close()` and use-after-`close()` must be compile-time rejected, not the
current do-nothing/UB behavior of calling `rt_*_free` twice on a raw `i64`.

## Scenarios

### resource SFFI pilot: File (unique R, nogc_sync_mut)

#### rejects a second close() on an already-closed handle at compile time

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a second close() on an already-closed handle at compile time


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a second close() on an already-closed handle at compile time")
val file = File.open("/tmp/does_not_matter.txt")?
file.close()
file.close()
assert_true(false)
```

</details>

### resource SFFI pilot: Image (unique R, nogc_sync_mut, design-doc exemplar)

#### rejects use-after-close at compile time

- rejects use-after-close at compile time


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects use-after-close at compile time")
val image = Image.open("/tmp/does_not_matter.png")?
image.close()
val w = image.width()
assert_true(false)
```

</details>

### resource SFFI pilot: CudaPrimaryContext (foreign RC via *R, nogc_sync_mut)

#### shares one foreign-refcounted context across two owners

- shares one foreign-refcounted context across two owners


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shares one foreign-refcounted context across two owners")
val ctx1 = CudaPrimaryContext.open(0)?
val ctx2: *CudaPrimaryContext = ctx1
ctx1.close()
ctx2.close()
assert_true(false)
```

</details>

### resource SFFI pilot: AtomicCounter (wrapper RC via *R, gc_async_mut)

#### allocates a wrapper control block since gc_async_mut permits allocation

- allocates a wrapper control block since gc_async_mut permits allocation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates a wrapper control block since gc_async_mut permits allocation")
val counter1 = AtomicCounter.open(0)?
val counter2: *AtomicCounter = counter1
counter1.close()
counter2.close()
assert_true(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `987d9bd10c34e2792344170b5ed6688b74631671cdfa8b1c045d74a82f01ea6c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `987d9bd10c34e2792344170b5ed6688b74631671cdfa8b1c045d74a82f01ea6c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `987d9bd10c34e2792344170b5ed6688b74631671cdfa8b1c045d74a82f01ea6c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl
mirror: doc/06_spec/01_unit/compiler/resource/resource_sffi_pilot_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/resource/resource_sffi_pilot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/resource/resource_sffi_pilot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a second close() on an already-closed handle at compile time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects use-after-close at compile time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shares one foreign-refcounted context across two owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
