# Structural Compute — Parallel Lane Plans

**Date:** 2026-07-31 · **Status:** Proposed

Per-lane implementation plans for the tagged structural-compute platform.
Parent documents (authoritative for contracts and semantics):

- Architecture: `doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md`
- GPU web lane: `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md`
- Conservative render plan (unchanged): `doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md`

## Lanes

| # | Plan | Covers (architecture lanes) |
|---|---|---|
| 1 | `parser_framework_plan.md` | PARSE — ParseDialect runtime, SIMD/GPU lex, incremental parse |
| 2 | `simple_compiler_offload_plan.md` | SIMPLE — compiler stage offload (§11.5 matrix), AOP QueryIR, optimizer |
| 2b | `clang_bridge_plan.md` | CLANG-AST + LLVM — C/C++ bridge (separate from Simple compiler offload) |
| 3 | `html_css_parser_plan.md` | HTML-DOM + CSS-STYLE parse side (WebScene W3/W4 alignment) |
| 4 | `layout_framework_plan.md` | LAYOUT framework — islands, profiles, dependency scheduling |
| 5 | `web_layout_manager_plan.md` | Browser incremental layout manager + GPU kernels (W5) |
| 6 | `link_manager_plan.md` | LINK — GraphResolveCore, SMF linker, StyleLinker |
| 7 | `gpu_mmu_plan.md` | PLACE — Object VM, residency tiers, SSD backends |
| 8 | `webrender_gpu_offload_plan.md` | Remaining WebScene offload — events, script, media, DrawIR v3, backends |

## Frozen contracts

| Group | Lane | Contract document |
|---|---|---|
| `EntityRef`/`EntityKey`/`SnapshotId`, `TagSchema` + tag encoding | ID-TAG | `doc/05_design/platform/structural_compute/identity_tagmap_contract_v1.md` |

The ID-TAG contract document also carries the **CONVENTIONS** section (module
layout, naming, serializer style, golden-vector format and location, schema
versioning) that the remaining nine contract groups follow.

## Shared rules (all lanes)

1. **Contract freeze first.** No lane implements against unfrozen contracts
   (architecture §26; WebScene C0). Contract changes = new schema version.
2. **Exclusive path ownership.** Owned paths listed per plan; only integration
   owners touch shared entrypoints (exports, driver/CLI, MDSOC bindings,
   browser composition roots).
3. **CPU reference is the oracle** and is never deleted. Every accelerated
   stage ships parity tests against it.
4. **No silent fallback.** `cpu_selected` by cost policy is not `gpu_fallback`;
   every fallback carries a reason receipt.
5. **Three modes everywhere:** `cpu_reference`, `hybrid_vector_gpu`,
   `resident_gpu` — same observable results.
6. **ADR-004 value semantics in every table/arena implementation.** Mutating a
   value reached through a dict index or an indexed tuple/struct field is
   silently lost; use the write-back idiom. Lint COLL019 flags the pattern.
   See `doc/04_architecture/adr/ADR-004-indexed-access-value-semantics.md`.

## Variable execution configuration

Offload level is **runtime/config selection, not a build variant** — one
binary, mode chosen per stage via `ExecutionProfile` (architecture §21,
SDN profiles in Appendix D):

```text
full offload   resident_gpu       fallback: hybrid → cpu_reference
balanced       hybrid_vector_gpu  fallback: cpu_reference
cpu only       cpu_reference      no GPU dependency; always available
auto           policy selector over measured crossover curves
```

Applies to the Simple compiler, web renderer, layout, and linker alike. On the
web side the same spectrum is expressed by the WebScene feature flags and
fallback levels (flags off = current CPU path byte-identical; L4 document
compatibility = full CPU render; strict profile = L0/L1 only). All modes must
produce identical observable results; `cpu only` must work with no GPU
present.

## Dependency order

```text
contract freeze (arch §26 + WebScene C0)
    ├─ gpu_mmu ───────────────┐ (all resident-GPU work depends on it)
    ├─ parser_framework ──┬─ simple_compiler_offload
    │                     ├─ html_css_parser ─┬─ web_layout_manager
    │                     └─ clang_bridge     │
    ├─ layout_framework ───────────────────────┘
    ├─ link_manager (simple_compiler_offload's link stage lands here)
    └─ webrender_gpu_offload (consumes parser/layout/link/mmu outputs)
```

CPU-reference deliverables in every lane are wave-1 and do not wait on
`gpu_mmu`; only resident-GPU tiers do.

Operator guide for the generic layout lane:
`doc/07_guide/platform/structural_compute/layout_framework.md`.

Browser consumer guide:
`doc/07_guide/platform/structural_compute/web_layout_manager.md`.
