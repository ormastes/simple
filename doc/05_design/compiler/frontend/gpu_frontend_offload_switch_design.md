# GPU Frontend Offload Switch — Detail Design

**Date:** 2026-09-05 · **Lane:** `gpu_frontend_offload` · **Status:** frozen for Wave 0
**Research:** `doc/01_research/compiler/parser/gpu_frontend_offload_switch_gap_2026-09-05.md`
**Extends:** `doc/05_design/simple_compiler_offload.md` (ADR-OFF-4/5), parser framework design.

## Decision

One typed switch selects whether the compiler frontend (lex/structure + parse
stages) may leave the CPU. It resolves **into the existing
`CompilerOffloadProfile`** (`src/compiler/00.common/structural_contracts/offload_profile.spl`)
— no new mode enum. Default is **off**; the Rust seed, bootstrap, and every
CPU-only host run unchanged. "On" never silently succeeds: while the GPU parse
path is unimplemented, the switch records a demotion receipt with
`fallback_reason = "parse_mode_unimplemented"` under `AllowCpu`, and returns an
error under `RequireRequested` (mirrors `EnforceMode` in
`src/lib/nogc_async_mut/compute/exec_target.spl:47,192,265`).

## Inputs and precedence

| Source | Key | Values |
|---|---|---|
| CLI | `--frontend-offload=<v>` | `off` \| `on` (alias `hybrid`) \| `resident` \| `auto` |
| env | `SIMPLE_FRONTEND_OFFLOAD=<v>` | same |
| project config | `simple.sdn` → `frontend: { offload: <v> }` | same — **Wave 1**: resolver slot exists and is tested; the driver forwards `""` until `ProjectContext` is threaded into the parse pipeline (GFO-005) |
| default | — | `off` |
| CLI | `--frontend-offload-fallback=<p>` | `allow-cpu` (default) \| `require-requested` |
| env | `SIMPLE_FRONTEND_OFFLOAD_FALLBACK=<p>` | same |
| config | `frontend: { offload_fallback: <p> }` | same — **Wave 1** (GFO-005) |

Precedence: CLI > env > config > default. The CLI layer only **sets the env
var** (same pattern as `SIMPLE_FRONTEND_CACHE` in `src/app/cli/native_build_main.spl:455`),
so the driver has one read path. Unknown text is an error, never a silent `off`.

## Frozen contract (new file, pure, no env/rt access)

`src/compiler/00.common/structural_contracts/frontend_offload_switch.spl`

```simple
struct FrontendOffloadInputs:
    cli: text            # "" when absent
    env: text
    config: text
    fallback_cli: text
    fallback_env: text
    fallback_config: text

struct FrontendOffloadSwitch:
    mode: OffloadMode        # CpuReference | HybridVectorGpu | ResidentGpu
    auto: bool               # true only for "auto"; mode is the evidence-less floor (CpuReference)
    fallback: OffloadFallbackPolicy
    source: text             # "cli" | "env" | "config" | "default"
    raw: text                # the winning input text

fn parse_frontend_offload_value(raw: text) -> Result<FrontendOffloadSwitch, text>
fn resolve_frontend_offload(inputs: FrontendOffloadInputs) -> Result<FrontendOffloadSwitch, text>
fn frontend_offload_profile(switch: FrontendOffloadSwitch) -> CompilerOffloadProfile
    # cpu_only_profile() with stage_modes[LexStructure] and [Parse] set to switch.mode
fn frontend_offload_decision(switch: FrontendOffloadSwitch, gpu_parse_available: bool) -> Result<OffloadDecision, text>
    # off            -> selected=CpuReference, fallback_reason=""
    # auto           -> AllowCpu: selected=CpuReference, reason="auto_profile_not_implemented_wave_1"
    #                   (no retained crossover evidence; never a silent "off")
    #                   RequireRequested: Err("frontend_offload_required_mode_unavailable: auto")
    # on, !available -> AllowCpu: selected=CpuReference, reason="parse_mode_unimplemented"
    #                   RequireRequested: Err("frontend_offload_required_mode_unavailable: <mode>")
    # on,  available -> selected=requested, reason=""
fn frontend_offload_parse_mode_text(decision: OffloadDecision) -> text
    # OffloadMode -> PARSE_MODE_CPU_REFERENCE | PARSE_MODE_HYBRID_VECTOR_GPU | PARSE_MODE_RESIDENT_GPU
fn frontend_offload_receipt_line(decision: OffloadDecision, source: text) -> text
    # "[frontend-offload] requested=<m> selected=<m> reason=<r> source=<s>"
```

`gpu_parse_available` is **false in Wave 0** (executors are fail-closed stubs);
it becomes `parse_run` admission once `parser_framework` lands its contracts v2.

## Driver wiring

`src/compiler/80.driver/driver_source_pipeline_parsing.spl` (clean file):

- `driver_frontend_offload_switch() -> Result<FrontendOffloadSwitch, text>` reads
  the two env keys through the existing `_sffi_env_get` facade and forwards
  `config: ""`: the parse pipeline holds no `ProjectContext`
  (`80.driver/project.spl` loads `simple.sdn` only for the top-level driver),
  so reading `frontend.offload*` is Wave 1 (GFO-005) — thread the loaded
  config's text through, no new parser.
- `driver_frontend_offload_decision() -> Result<OffloadDecision, text>` calls
  `frontend_offload_decision(switch, FRONTEND_OFFLOAD_GPU_PARSE_AVAILABLE)` on
  every call (the decision is recomputed; only the receipt line is memoized
  process-wide so `dtrace` prints it once per process, parse-shard children
  included).
- On `Err`, the driver fails the compile with the message (fail-closed).
- On `Ok`, the receipt line goes through `dtrace(...)` (env-gated
  `SIMPLE_INTERP_TRACE=1`). The native-build warm receipt
  (`src/app/cli/native_build_warm_receipt.spl`) folds the same decision into its
  warm-cache identity digest through the shared `frontend_offload_rows(env,
  fallback)` helper (four canonical rows, or one `frontend_offload_error=` row)
  — one derivation, two consumers.
- `frontend_offload_profile` builds the `CompilerOffloadProfile` for the Wave-1
  per-stage dispatcher; in Wave 0 the only production consumer is the decision,
  so the profile helper has no driver caller yet (tested, not wired).
- **No GPU/runtime initialization on any path in Wave 0.** When `selected ==
  CpuReference` the driver continues into the legacy `core_frontend_parse`.

## Receipts and parity

`OffloadDecision` is the single observable. `StageReceipt.deterministic_hash`
must be identical for `off` and `on+AllowCpu` on the same source (both run the
oracle), which is the parity invariant later waves must keep.

## Non-goals (Wave 0)

No kernels, no SIMD masks, no contracts v2, no grammar generator, no sosix
changes. GPU backends will obtain host I/O through the sosix host proxy designed
by the sosix lane; this switch only decides *whether* that path is requested.

<!-- sdn-diagram:gpu-frontend-offload-switch-flow -->
```sdn
cli --frontend-offload -> env SIMPLE_FRONTEND_OFFLOAD
{env, simple.sdn frontend.offload, default off} -> resolve_frontend_offload -> FrontendOffloadSwitch
FrontendOffloadSwitch -> frontend_offload_profile -> CompilerOffloadProfile
FrontendOffloadSwitch + gpu_parse_available -> frontend_offload_decision -> OffloadDecision | Err
OffloadDecision -> {dtrace receipt, warm receipt row, ParseRequest.mode text}
```
