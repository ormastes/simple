# GPU WebScene Contracts Design

**Date:** 2026-07-31  
**Status:** Frozen (C0)  
**Contract Owner:** C0 contract-freeze group  

## Related Documents
- `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md` — system plan (§1 healthy receipts, §7 fallback hierarchy, §14 acceptance gates)
- `doc/03_plan/platform/structural_compute/README.md` — shared structural-compute rules (rule 4: no silent fallback)
- `doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md` — MDSOC+ ownership and isolation

## Overview

The GPU WebScene system defines five frozen contract files that encode input packets, state mutations, host-effect requests, capacity bounds, and receipt schemas. Each contract carries an immutable schema-version constant and is read-only until a formal version bump. This design enables parallel implementation without coordination: each agent works on its assigned capsule or compilation layer, contracts remain stable, and all fallback and overflow scenarios produce explicit diagnostic receipts.

---

## Contract Files

### 1. gpu_web_ports.spl — Input, Mutation, and Host-Effect Packets

**Purpose:** Sealed packet records for event input, GPU-side state mutations, and CPU-side effect requests.

**Schema Version:** `GPU_WEB_PORTS_SCHEMA_VERSION = "simple-gpu-web-ports-v1"` (ID: 1)

**Records:**
- `GpuInputEvent` — device input (pointer, key, text) with scene-generation version and sequence number
- `GpuMutation` — transactional state mutation (node_id, field_id, operation, 64-bit value)
- `GpuHostEffectRequest` — CPU OS operation (fetch, file, clipboard, IME, accessibility) with continuation ID
- `GpuHostEffectCompletion` — CPU effect result with status code and optional payload
- `GpuResourcePacket` — compressed media bytes (JPEG, WebP, PNG, WebM) with declared dimensions

All variable-length data (text, payload bytes) lives in fixed arenas referenced by (offset, length), never host pointers.

**Frozen Constant Enums:**
- `GPU_EVENT_KIND_*` (POINTER_MOVE, KEY_DOWN, TEXT_INPUT, TIMER, HOST_EFFECT_COMPLETION)
- `HOST_EFFECT_*` (FETCH, FILE, CLIPBOARD, IME, ACCESSIBILITY_SNAPSHOT)

### 2. gpu_web_receipt_contract.spl — Epoch, Fault, and Overflow Receipts

**Purpose:** Diagnostic records reporting frame completion, feature failures, capacity breaches, and fallback routing.

**Schema Version:** `GPU_WEB_RECEIPT_SCHEMA_VERSION = "simple-gpu-web-receipt-v1"` (ID: 1)

**Records:**
- `GpuSceneEpochReceipt` — frame completion with: mutations applied, host effects requested, fallback level, route decision, deterministic hash (lo/hi)
- `GpuFaultReceipt` — feature or device failure with: capability bit (0 if not feature-scoped), subtree node ID, reason code, detail offset/length
- `GpuOverflowReceipt` — capacity bound breach with: bound ID (names the bound), requested count, manifest limit

**Fallback Hierarchy (L0–L5):**

| Level | Trigger | GPU Residence | Fallback Scope |
|-------|---------|---------------|----------------|
| L0 | Supported epoch | Entire scene | None |
| L1 | Host effect needed | Scene minus effect | Only that OS operation |
| L2 | Unsupported codec/text | Scene minus feature | One bounded resource result |
| L3 | Unsupported CSS/layout | Scene minus subtree | One frozen subtree artifact |
| L4 | Unsupported JS or hard profile | Document | Entire document |
| L5 | Device lost/OOM/fault | None | Backend restart or CPU renderer |

**Pass Predicates:**
- `gpu_fallback_is_strict_pass(level: u16) -> bool` — true if L0 or L1 (GPU-native or host-effect only)
- `gpu_fallback_is_compat_pass(level: u16) -> bool` — true if L0–L3 (reported subtree compat acceptable)

**Route Constants:**
- `GPU_ROUTE_GPU` — GPU handled entire epoch (no fallback)
- `GPU_ROUTE_CPU_SELECTED` — CPU chosen by cost policy (NOT a fallback; must be distinguished from failures)
- `GPU_ROUTE_GPU_FALLBACK` — GPU attempted but fell back to CPU

`draw_ir_v3_execution_route.spl` adds a stricter execution-selection model for
DrawIR-v3 documents. In addition to the route, it defines:

- `DrawIrV3ExecutionProfile` (`cpu_reference`, `hybrid_vector_gpu`,
  `resident_gpu`) with an explicit `strict` flag
- a `DrawIrV3RouteDecision` with `route`, `executed_mode`,
  `fallback_level`, `reason_code`, and `strict_pass`
- the invariant that route and reason-class must stay partitioned:
  - `gpu-selected` must carry policy reasons (`100..199`)
  - `gpu-fallback` must carry denial reasons (`200..299`)

Design consequence: `"cpu_selected"` is a valid first-class success mode only when
the profile explicitly requests/justifies CPU; it must not be used to hide missing
device or denied capability failures. `accepted` on the submit receipt follows
this split (`true` for CPU-selected and GPU routes; `false` for any fallback).

### 3. gpu_web_capacity_manifest.spl — No-Reallocation Capacity Contract

**Purpose:** Explicit policy bounds for finite no-reallocation arenas. Kernel A counts outputs, Kernel B exclusive-prefix-scans, Kernel C verifies total ≤ capacity. Exceeding a bound triggers a rejection with a diagnostic receipt.

**Schema Version:** `GPU_WEB_CAPACITY_MANIFEST_SCHEMA_VERSION = "simple-gpu-web-capacity-v1"` (ID: 1)

**Manifest Records:**
- `GpuWebCapacityManifest` — policy bounds: max_input_bytes, max_nodes, max_css_rules, max_layout_boxes, max_draw_commands, max_glyphs, max_mutations_per_epoch, scratch areas (parser_scratch_bytes, style_scratch_bytes, layout_scratch_bytes, scan_scratch_bytes, backend_preprocess_bytes)
- `GpuWebCapacityPlan` — Kernel A+B result: exact arena totals if Kernel D emits (field names mirror Manifest without `max_` prefix for unambiguous breach receipts)

**Honesty Rule (Structural-Compute Shared Rule 3):**

Kernel C (CPU reference oracle and GPU implementation) **never** truncates, clamps, or reallocates. Exceeding a bound triggers immediate rejection carrying a `GpuOverflowReceipt` naming the bound, the requested amount, and the limit. Violating this rule defeats the no-reallocation guarantee and is a defect.

**Capacity Sources:**

| Phase | Source |
|-------|--------|
| Compile time | Fixed GUI/theme recipes, static HTML/CSS templates, GPU-safe Simple handlers |
| Load time | Response size, declared resource headers, viewport/locale/font profile, dynamic-content policy limits |
| Backend session creation | Device alignment requirements, descriptor limits, indirect/preprocess GPU queries |

---

## Contract Semantics and Enforcement

### Strict GPU Mode

Accepts only L0 or L1 on all admitted pages:
- Full GPU success or host-effect only
- Any L2–L5 occurrence fails the test
- No false GPU success after silent fallback

### Standards Compatibility Mode

Accepts L0–L3 and reports all occurrences:
- GPU-native or host-effect (L0–L1)
- Unsupported codec/text service (L2)
- Unsupported CSS feature subtree (L3)
- L4–L5 treated as full fallback (explicit, not hidden)

### Device Failure

- L5 allowed but never reported as GPU success
- Fault receipt names the capability bit (or 0 if device-scope) and reason code
- System may restart backend or fall back to CPU renderer; the choice is explicit

### CPU-Selected vs GPU-Fallback Distinction

**CPU_SELECTED:** Work intentionally routed to CPU by cost policy (e.g., small scene, CPU-local execution cheaper). Reported separately from fallback; not a failure signal.

**GPU_FALLBACK:** GPU attempted the work and failed. Always paired with a fallback level (L1–L5) and reported as such.

Confusing the two is a defect: hiding a fallback as GPU_SELECTED or vice versa is data corruption.

---

## C0 Freeze Rule (Isolation Rule 3)

### Read-Only After Merge

After C0 is merged into main:

```
src/lib/common/ui/gpu_web_ports.spl
src/lib/common/ui/gpu_web_capacity_manifest.spl
src/lib/common/ui/gpu_web_receipt_contract.spl
src/lib/common/ui/draw_ir_v3.spl (or draw_ir_v3_ports.spl)

doc/04_architecture/ui/gpu_web_scene_ports.md
doc/05_design/ui/gpu_web_scene_contracts.md
```

All are read-only. No agent may edit these files in place.

### Schema Version Bump Process

To evolve a contract:

1. Create a new schema version constant (e.g., `GPU_WEB_PORTS_SCHEMA_VERSION = "simple-gpu-web-ports-v2"`)
2. Add new records or fields in a separate struct (e.g., `GpuInputEventV2`)
3. Update architecture and design docs with the new version
4. Merge as a separate change with explicit version-bump commit message
5. All consumers and implementations must acknowledge the version change

Until that explicit bump, the current version is frozen.

### Rationale

Parallel agents work on disjoint capsule implementations (Program 1: W1–W11; Program 2: I1–I12). Frozen contracts prevent accidental drift and enable independent progress. Each agent trusts that the contract it consumes will not change mid-wave without explicit notification.

---

## Reference Oracles

Every accelerated GPU operation has a CPU reference implementation:

| Operation | Oracle Path |
|-----------|-------------|
| Event dispatch, hit query, mutation journal | src/lib/common/ui/gpu_event/ (cpu_oracle subdir) |
| DrawIR v3 count/scan/emit | src/lib/common/ui/draw_ir_v3/cpu_oracle/ |
| Selector match and cascade | src/lib/common/ui/gpu_style/ (cpu_oracle subdir) |
| Layout formatting contexts | src/lib/common/ui/gpu_layout/ (cpu_oracle subdir) |
| Media decode | src/lib/common/ui/gpu_media/ (cpu_oracle subdir) |

All oracles are maintained alongside their GPU counterparts and are never deleted. They are the authoritative source of truth for acceptance-gate parity comparisons.

---

## Implementation Dependencies

**Wave 0 (this group, C0):**
- Freeze all five contract files
- Lock all schema-version constants
- Document capsule visibility rules
- Commit ownership ledger at `doc/03_plan/agent_tasks/gpu_web_scene/ownership.sdn`

**Waves 1–3 (Program 1 & 2 parallel):**
- W1 (GPU-safe script compiler) validates `@gpu_event` against schema
- W2 (GPU event core) reads/writes GpuInputEvent, GpuMutation, receipts
- I1 (DrawIR v3 contract) defines command and table IDs; I2–I6 depend on I1
- W7 (GPU scheduler) emits GpuSceneEpochReceipt and capacity checks

All reference CPU oracles for parity gates.

---

## Acceptance Gates

**Functional parity:** CPU and GPU mutation journals byte-match for selected corpus.  
**Memory safety:** Zero realloc after scene seal; all capacity overflows fail closed with overflow receipt.  
**Fallback honesty:** Every fallback carries a diagnostic receipt; no silent SoftwareBackend calls.  
**Capacity honesty:** Every overflow receipt names the bound and measurement; no clamping or auto-grow.  
**Determinism:** Same event batch produces identical mutation bytes over 1,000 repetitions (validated via deterministic_hash fields).
