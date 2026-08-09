# ADR — Counterpart Conformance contract freeze (Wave 0, A0)

Date: 2026-08-09
Status: accepted
Supersedes: nothing. Constrains: all counterpart lanes (F1–F9, P1–P5, W*, V*, K*, Z*, M*, H*).

Design: `doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md`
Plan: `doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md`

## Decision

One conformance pipeline under Modern SSpec. No second differential framework. The
contracts below are **frozen**: a lane that needs one changed raises an ADR amendment
against this file rather than editing the contract in its own branch.

## Frozen artifacts

| Contract | Location | Frozen content |
|---|---|---|
| Counterpart records | `src/lib/common/spec/evidence/counterpart/model.spl` | Three evidence planes, boundary ID, provider/component manifests, conversion loss, relations, oracle authority, plan, run |
| Modern SSpec evidence | `src/lib/common/spec/evidence/model.spl` | Unchanged. Counterpart work is additive only |
| Adapter ABI | `tools/counterpart/sdk/c/simple_counterpart_abi.h` | `scf_api_v1`, `scf_get_api`, ABI version 1 |
| Boundary ID format | this ADR + `parse_boundary_id` | `<domain>.<mdsoc-layer>.<stage>@<schema-version>` |
| Conversion loss enum | `ConversionLoss` in the model | `identity < representation_only < canonicalizing < semantic_projection < diagnostic_only` |
| Extension schema | `COUNTERPART_EXTENSION_SCHEMA` | `simple.sspec.counterpart.v1`, opaque, refs only |

## Rationale for the non-obvious choices

**Adapter library, not upstream dlopen.** Chrome is process-driven, Vulkan dispatches
through loader/layer/ICD, and SPIRV-Cross does not promise a stable C++ ABI. A single
Simple-owned `libsimple_counterpart_<provider>.so` gives every provider one stable ABI
regardless of whether the backend is in-process, a worker, a browser, QEMU, or remote
hardware. Tests never guess an upstream symbol name.

**A dedicated ABI shim, not `DynLib.call_n()`.** The existing loader's call interface is an
integer array returning an integer. It cannot express pointer+length buffers, typed result
ownership, output writers, timeouts, schema negotiation, structured errors or crash
containment. Widening it with raw pointers would spread unsafety across every caller; a
narrow `src/runtime/counterpart_abi_runtime.c` keeps pointers on one side of one wall.

**Three separate receipt planes.** Logical equality and physical execution are independent.
Collapsing them is exactly how a GPU lane passes while silently running on CPU, so
`ExecutionReceipt` is a first-class record with a hard gate
(`execution_receipt_gpu_gate_failures`) rather than a per-domain convention.

**Loss rank is ordered and the exactness rule lives in one function.** `relation_requires_exactness`
plus `relation_max_permitted_loss_rank` are consulted by both the converter graph and the
relation engine. Two copies of that rule would drift, and the drift direction is always
toward accepting a lossy route for an exact claim.

**`independence_group`, not provider count.** Two wrappers over one upstream engine are one
reference. Counting them as two manufactures false independence, which is the specific
common-mode failure a differential suite is supposed to detect.

**Authority rank over consensus.** Three implementations sharing one defective upstream are
weaker evidence than one known-answer vector. `oracle_authority_rank` makes consensus
diagnostic by construction.

**Unavailable is never pass, and crashed is not unavailable.** `ProviderStatus` keeps
`crashed`, `timed_out` and `rejected_manifest` distinct from `unavailable` so a real defect
cannot be normalized into "provider not present."

## Consequences

- Production modules must contain no foreign provider imports or types; all upstream
  dependencies live in the test-only capsule and under `tools/counterpart/`.
- Downloaded source and build products live under `build/counterparts/`, never in the owned
  source tree.
- Central registries are generated from per-provider descriptor files, so domain lanes add a
  descriptor instead of editing one shared registry.
- Every lane must ship a sabotage that turns green to red; "the adapter ran" is not an
  acceptance criterion.

## Amendment procedure

Open a PR that (1) edits this ADR's frozen-artifact table, (2) states which lanes are
invalidated, and (3) lands the contract change and all lane fixes together. A0 (architecture
captain) is the reviewer of record.
