# GPU Frontend Offload Switch — Gap Research (2026-09-05)

**Purpose:** reconcile the two 2026-09-01 research docs
([architecture](gpu_frontend_offload_unified_parser_architecture_2026-09-01.md),
[work-table design](gpu_resident_frontend_cpu_work_table_parser_unification_2026-09-01.md))
with the tree at `973f2471db1`, and isolate the smallest shippable slice: an
**on/off-able frontend offload switch** that defaults to CPU and never hides a
fallback. Sosix host-proxy unification is a separate agent's lane; GPU backends
will reach host I/O through it later and it is only *referenced* here.

## Audit claims re-verified at `973f2471db1`

| Claim (docs pinned to `1b12bd36bc8`) | Now | Consequence |
|---|---|---|
| `src/lib/parser/parser.spl` unresolved | still absent; `src/lib/common/parser/parser.spl` exists | interpreter fork is real; not touched by the switch |
| reduced "TreeSitterParser" under `compiler_rust/lib/std/.../treesitter/` | still present, not renamed | GFPU-904 / TSR-001 still open |
| `treesitter.spl`, `parser/partial.spl`, `parser/recovery.spl` | present; `treesitter/*` and `core/lexer*.spl` are **dirty in a peer session** | switch lane must not edit them |
| structural-parse executors are Wave-1 stubs | confirmed: 1558 lines total, `structural_index/parallel_lex/incremental/auto_profile` fail-closed stubs | GPU path honestly returns `parse_mode_unimplemented` |
| `contracts.spl` enum vs `parse_types.spl` text modes disagree | confirmed: `ParseExecutionMode{Scalar,Simd,Gpu,Incremental,Auto}` vs `PARSE_MODE_{cpu_reference,hybrid_vector_gpu,resident_gpu}` | vocabulary conflict below |
| offload profile contract exists | `structural_contracts/offload_profile.spl`: `OffloadMode{CpuReference,HybridVectorGpu,ResidentGpu}`, `OffloadFallbackPolicy{AllowCpu,RequireRequested}`, `OffloadDecision`, `cpu_only_profile()` — **clean, unowned by the peer** | the switch resolves *into this* |
| SIMD UTF base | `src/lib/encoding/simd_text_sffi.spl` + `runtime_simd_utf8.c` present | reuse for Wave 5/6 |
| device scan primitive | `compute_exclusive_scan<T>(…, target: ExecTarget)` in `nogc_async_mut/compute/compute_algo_ext.spl:91` | backend-neutral scan port already exists |
| suggest/require precedent | `exec_target.spl:47 EnforceMode`, `:192 resolve_exec_target`, `:265 exec_target_from_env` | switch fallback mirrors it |

## Vocabulary decision

Three vocabularies coexist. The repo's `OffloadMode` (doc 1's
`cpu_reference|hybrid_vector_gpu|resident_gpu|auto`) is the **mode axis**;
scalar vs SIMD is a **backend axis inside hybrid** (doc 1 §18.7). Doc 2's
`cpu-simd`/`gpu-verify` names are not carried forward: SIMD is a backend,
`verify` is an assurance policy. `off` ≡ `CpuReference`, `on` ≡
`HybridVectorGpu`. The current handwritten parser **is** `cpu_reference`
(ADR-OFF-4, doc 2 I-01); a generated scalar executor is a later, separate
executor and never replaces the oracle.

## Knowledge routes

`doc/00_llm_process/knowledge_registry.sdn` routes `gpu_offload_check` only;
no `parser_framework` / `simple_compiler_offload` route exists — recorded as a
research gap, not a blocker. Nearest expert: `feature_expert/gpu_offload_check`.

<!-- sdn-diagram:gpu-frontend-offload-switch-context -->
```sdn
switch_inputs: [cli --frontend-offload, env SIMPLE_FRONTEND_OFFLOAD, simple.sdn frontend.offload, default off]
resolver: resolve_frontend_offload -> FrontendOffloadSwitch -> CompilerOffloadProfile.stage_modes[LexStructure, Parse]
decision: frontend_offload_decision -> OffloadDecision {requested, selected, fallback_reason}
wave0_truth: {on: selected=CpuReference reason=parse_mode_unimplemented, off: no GPU init, require: Err}
blocked_on: peer parser_framework landing (contracts v2)
```
