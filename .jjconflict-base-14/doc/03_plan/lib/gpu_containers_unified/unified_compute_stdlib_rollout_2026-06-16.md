# Implementation Plan — Unified CPU/GPU Compute Stdlib (CCCL Parity)

**Phase:** 03_plan · **Domain:** lib · **Topic:** gpu_containers_unified · **Date:** 2026-06-16
**Research:** `doc/01_research/lib/gpu_containers_unified/gpu_containers_algorithms_stdlib_cuda_parity_2026-06-16.md`
**Requirements:** `doc/02_requirements/lib/gpu_containers_unified/unified_compute_stdlib_draft.md` · `doc/02_requirements/nfr/unified_compute_stdlib_parity_verification_draft.md`

## 0. Strategy in one paragraph

Build a single generic, policy-switchable compute surface in the `nogc_async_mut` default
tier that compiles through the existing `gpu_portable_compute` MIR / `@gpu_kernel` path (no
fork). Deliver each `{algorithm} × {backend}` cell as an isolated unit. **CUDA is built
first** and becomes the **differential-test oracle**; pure-Simple, Vulkan, Metal cells are
each verified bit-exact (or within declared float tolerance) against it before merge. Bugs
found en route (iterator protocol, CPU-masquerading `gpu_*`, atomics, f64) are fixed in the
same waves, not deferred.

SPipe tracking: `.spipe/gpu_containers_unified/state.md` (AC-1…AC-7). This plan realizes
the dependency flow below — prerequisites gate the CUDA oracle, which gates every other
backend cell, each passing the Opus verification gate before merge.

<!-- sdn-diagram:id=gpu_containers_unified.plan -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_containers_unified.plan hash=sha256:auto render=ascii
@layout dag
@direction LR

PreWork_P1_P5 -> W1_CUDA_oracle
PreWork_P1_P5 -> Container_track
W1_CUDA_oracle -> W2_pure_Simple
W1_CUDA_oracle -> W3_Vulkan
W1_CUDA_oracle -> W4_Metal
W2_pure_Simple -> Opus_verify_gate
W3_Vulkan -> Opus_verify_gate
W4_Metal -> Opus_verify_gate
Container_track -> Opus_verify_gate
Opus_verify_gate -> Merge
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_containers_unified.plan hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## 1. Pre-work — unblock prerequisites (must land before the cell grid)

These gate everything; do them first, in order, each with its own bug/feature doc.

| Step | Work | Blocks | Verify |
|---|---|---|---|
| P1 | **Single backend resolver** — collapse the 4 selectors (`SIMPLE_2D_BACKEND`, `gpu_target_metadata` order, `@gpu_kernel(target:)`, BLAS provider) into one `ExecTarget` resolver. Keep landed `vulkan,metal,cuda,hip,opencl→cpu` default for `Auto`. | FR-3 | env/config matrix test selects expected backend |
| P2 | **`ExecTarget` policy type** + threading it through one trivial algorithm (`for_each`) end-to-end on Cpu + Cuda. | FR-2/3, all cells | `for_each` runs CPU and CUDA by policy only |
| P3 | **Iterator protocol bug** (`for x in <struct>` iterates 0×, research B1). | generic algos over containers | spec: custom container iterates N elements |
| P4 | **f64 reliability triage** (research B5) — at minimum document which backends are trustworthy; gate float-reduction cells on it. | numeric correctness | f64 reduce matches CPU reference |
| P5 | **Rename/honor `gpu_*`** — make existing `gpu_reduce/scan/sort` either truly dispatch by policy or be renamed `cpu_*` (research B3 perf bug). | NFR-3 honesty | no `gpu_`-named fn silently on CPU |

## 2. The cell grid (parallel unit of work)

Rows = algorithms (Thrust parity), columns = backends. Each cell = **one disjoint file
scope** (required for parallel agents; cf. `feedback_parallel_scope_partition`).

```
                 CUDA(oracle)   pure-Simple   Vulkan   Metal
transform           W1             W2           W3       W4
reduce              W1             W2           W3       W4
inclusive_scan      W1             W2           W3       W4
exclusive_scan      W1             W2           W3       W4
sort/stable_sort    W1             W2           W3       W4
copy_if/remove_if   W1             W2           W3       W4
unique/partition    W1             W2           W3       W4
find/lower_bound    W1             W2           W3       W4
reduce_by_key       W1             W2           W3       W4
```

Container/type cells (libcu++ parity) run alongside as a parallel track:
`Array<T,N>`, `Span<T>`, `MdSpan<T>`, `InplaceVector`, `Bitset`, `Complex<T>`,
`Atomic<T>` + `Barrier/Latch/Semaphore` (research B4), `random`.

## 3. Waves (delivery order = research §3a)

- **W1 — CUDA cells (the oracle).** Implement each algorithm for the CUDA backend (FFI to
  Thrust/CUB *or* emitted `@gpu_kernel` — decided in `/arch`, open Q3). Each W1 cell ships
  with a golden test capturing its output → becomes the oracle.
- **W2 — pure-Simple cells.** CPU reference impl, generic over `T`. Verified against the W1
  oracle (NFR-1). This is also where most stdlib value lands (works with no GPU present).
- **W3 — Vulkan cells.** SPIR-V via existing `vulkan_backend`. Verified vs oracle.
- **W4 — Metal cells.** MSL via existing metal session. Verified vs oracle.
- **CUB-block track** (research B8): expose block-level cooperative reduce/scan; can begin
  after P2, parallel to W2.

Within a wave, cells are independent → fan out. Across waves, a backend cell cannot start
until its CUDA oracle (W1) exists.

## 4. Parallel-model staffing + verification gate

Per the user's "haiku in parallel, opus verifies" model:

1. **Implementer agents (haiku/sonnet):** one agent per cell, disjoint file scope, given the
   algorithm spec + the CUDA oracle golden file + `advisor()` access.
2. **Opus verification gate (per cell, before merge):**
   - run differential test vs CUDA oracle (NFR-1: bit-exact int/sort, tolerance for float);
   - run perf check vs CPU reference (NFR-3: slower-than-CPU = perf bug filed);
   - code review for fork-avoidance (NFR-4) and naming honesty (NFR-3).
   - On mismatch/missing-in-strict → fail-closed `rt_exit 70`; cell does not merge.
3. **Orchestrator:** verify+commit on agents' behalf (memory: sub-agents leave work
   uncommitted), one commit per cell, ≤5 files (force-push resilience).

## 5. Co-goal bug backlog → scheduled into waves

| Bug | When fixed | Doc |
|---|---|---|
| B1 iterator protocol | P3 (pre-work) | bug doc |
| B3 `gpu_*` CPU masquerade (perf) | P5 (pre-work) | bug doc |
| B5 f64 unreliable | P4 (pre-work) | tracked, gates float cells |
| B6 array.get(>=1) corruption | before W2 container cells | bug doc |
| B4 no atomics/barriers | container track (W2) | feature doc |
| B7 four-resolver debt | P1 (pre-work) | refactor doc |
| B8 block-level cooperative ops | CUB-block track | feature doc |

## 6. Milestones / exit criteria

- **M0:** P1–P5 landed; `for_each` runs CPU+CUDA by policy only. (Switchability proven.)
- **M1:** W1 CUDA oracle complete for all algorithms; golden tests committed.
- **M2:** W2 pure-Simple complete + verified → **stdlib usable with no GPU** (the broad win).
- **M3:** W3 Vulkan + W4 Metal verified.
- **M4:** libcu++ type parity (container track) complete; co-goal bug backlog closed.
- **Done:** parity table (research §1a/1b/2b) has no "missing" rows that were in scope; every
  backend differential-passes the CUDA oracle; no `gpu_`-named CPU masquerade remains.

## 7. Risks

- **Open Q3 (FFI-to-Thrust vs emit-kernel)** changes W1 effort drastically — resolve in
  `/arch` before W1 starts.
- **Float tolerance contract (Q4)** must be fixed before W2 float cells, else differential
  tests are non-deterministic.
- **Parallel jj reconcile** can clobber uncommitted cells — commit per cell immediately
  (memory: multiple `feedback_*` entries).
- **f64 (B5)** may be deeper than triage; if so, descope float-heavy cells to int/f32 until
  fixed rather than ship unreliable numerics.

## 8. AC traceability (→ `.spipe/gpu_containers_unified/state.md`)

| AC | Covered by plan step(s) | Milestone |
|---|---|---|
| AC-1 single resolver | P1 | M0 |
| AC-2 generic algorithm surface | W1/W2 cell grid (§2) | M1/M2 |
| AC-3 libcu++ type parity | Container track (§3) | M4 |
| AC-4 config-only CPU/GPU switch | P2 (`for_each` proof) → all cells | M0 |
| AC-5 differential oracle + fail-closed | §4 verification gate | M1→M3 |
| AC-6 no perf-cliff / honest naming | P5, §4 perf check | M0/all |
| AC-7 co-goal bug backlog | §5 (B1–B8 scheduled) | spread M0→M4 |

## 9. SPipe phase checklist (this feature)

- [x] 1-dev — refined goal + ACs (`.spipe/gpu_containers_unified/state.md`)
- [x] 2-research — `doc/01_research/lib/gpu_containers_unified/…cuda_parity_2026-06-16.md`
- [ ] 3-arch — resolve Q1/Q3/Q4; module list + interfaces + ≥1 SDN component diagram
- [ ] 4-spec — failing SSpec `.spl` per AC (discriminating GPU-offload + parity oracles)
- [ ] 5-implement — pre-work P1–P5, then cell-grid waves W1→W4
- [ ] 6-refactor — dedup, ≤800-line files, naming, doc/wiki pass
- [ ] 7-verify — differential vs CUDA oracle, full suite, docgen scenario manuals
- [ ] 8-ship — jj commit per cell (≤5 files), tracking docs

## 10. Next

`/arch` to design the concrete surface (namespace, policy-as-value-vs-type, FFI vs kernel),
then `/impl` per wave. Open questions Q1–Q5 carried from research §6.
