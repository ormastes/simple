# Optimized dynamic observability aspects — plan (2026-10-28 rev 1.0) + applied-status audit (2026-11-06)

Status: plan accepted for alignment; implementation is NOT complete. Audited on
`release/1.0.0` @ `cfdbd29251a` (2026-11-06). This document condenses the
owner-supplied plan "Simple: Optimized Dynamic Aspects for Logging, Performance,
and Memory Profiling" and reconciles it with the newer repo docs:
[staged XRay plan](simple_xray_staged_implementation_plan_2026-11-03.md),
[XRay V1 status](xray_v1_integration_status_2026-11-03.md),
[parallel delivery plan](parallel_delivery_plan_2026-11-03.md),
[visibility plan](aspect_dynload_visibility_improvement_plan_2026-10-31.md),
[lane plan](aspect_dynload_lane_plan_2026-08-19.md) and the
[registry transaction](../../../04_architecture/compiler/aspect_dynload/registry_transaction_2026-08-22_tldr.md).
Where they disagree, the reconciliation in §3 wins over the condensed plan text.

## 1. Mode model

| Build contract | Meaning | Can enable later |
|---|---|---|
| `ERASED` | Sites, payload code and collector deps omitted from the artifact; payload never evaluated | no |
| `DYNAMIC_READY` (OFF) | Prepared sites compiled in, minimized (not zero) cost, no capture until activated | yes |
| `STATIC_ON` | Sites and capture always on | n/a |

Collection state is independent of residency:
`unloaded -> prepared/resident -> active -> draining -> resident/off` (the
plan's trailing `-> unloaded` is superseded, see §3). Load modes reuse the
existing `static / startup / manual / lazy_facet / lazy_patchable` routes; logs
and profiles default to `manual` or explicit `startup`; a resident-only
acquisition that finds nothing resident returns an explicit *unavailable*
result and never loads covertly.

## 2. Decisions (condensed)

- **D1** One backend-neutral observability contract on the EXISTING aspect-pack loader + `AspectRuntimeRegistry`; no second plugin system or dlopen path.
- **D2** Hot path never walks the plugin catalog or evaluates pointcut strings; structural selection is resolved at build/startup/load/policy change into a site-specific compact capture plan.
- **D3** Two OFF contracts (`ERASED`, `DYNAMIC_READY`) plus `STATIC_ON` (§1).
- **D4** Load modes as in §1; resident-only acquisition -> explicit unavailable.
- **D5** Collection state machine as in §1, independent of residency.
- **D6** Observation contracts: `machine` / `semantic` / `boundary`; a missing required semantic event is a compile/admission failure.
- **D7** Prepared sites call a small resident, non-instrumented capture shim that writes versioned bounded records; the collector consumes off-thread. Direct synchronous advice is opt-in only.
- **D8** Structural selectors -> typed matcher IR with read sets; dynamic predicates bounded; control-plane algorithm: validate, normalize, index-intersect, resolve sites, group plans, immutable site->plan map, publish via registry, activate delta only.
- **D9** `log`/event payload lowered to an intrinsic lazy region; the disabled path branches around the whole capture region; impure payload rejected.
- **D10** Two caches: `ObservationSurfaceKey` (build) and `ActivationPlanKey` (runtime); collector-body-only change never rebuilds core; positive AND negative selector dependencies recorded; `.rr` reverse index rebuildable, written atomically via sosix.
- **D11** LLVM XRay is ONE provider behind the facade (works with LTO/ThinLTO, no source-order guarantee); resident broker; capability tuple; strict W^X rejects the stock RWX patch path.
- **D12** Cranelift: guard/data-slot first; optional patchable-call adapter; no live-rewrite claims; generation-based JIT invalidation.
- **D13** Interpreter: per-code-object immutable event masks; host and guest domains separate.
- **D14** Logging: one facade (`src/lib/log.spl`, `nogc_sync_mut/log.spl` compat); four layers: build ceiling -> site activation -> runtime predicate -> sink policy; typed versioned records; producer path does no fs write, registry lock, allocation or formatting; per-stream overflow policy; resident emergency diagnostic path; redact before buffering.
- **D15** `joinpoint_slots.spl` hardening: pointer table is NON-executable data (no RW->RX for data), atomic release/acquire publication, atomic dispatch load, pointer width and page size from the host (no hard-coded 8 / 4096), retain a generation until readers quiesce.
- **D16** Activation transaction: 8 steps with rollback; disable != unmap; cut vs drain span policy.
- **D17** Performance aspect: sampling first, selective tracing second; wall / on-CPU / self / inclusive / count are separate metrics; finalization is a status, not a bool.
- **D18** Memory aspect: stats, sampling, exact observed cohort, heap snapshot; hooks at allocator ownership boundaries carrying `allocator_id` + sequence; baselines Since-T / enumerated / previously-resident; loss invalidates exactness; recursion guard; budgeted tracking.
- **D19** Records `SiteDescriptorV1` / `ObserverManifestV1` / `ActivationReceiptV1`; SDN policy fields; explain API for unavailable events.
- **D20** Vertical slice first (plan §18.1): one typed application event through `ERASED` / `DYNAMIC_READY`-OFF / load+activate / policy update / disable+drain via the real entrypoint.

### Acceptance IDs

OBS-001 ERASED absent + payload unevaluated · OBS-002 prepared/OFF no capture ·
OBS-003 activate -> record reaches collector via the real path · OBS-004 disabled
never traverses plugin/selector index · OBS-005 pointcut delta == full recompute
incl. negative/new · OBS-006 collector-body-only change, no core rebuild ·
OBS-007 LLVM no-LTO/full/Thin events + live maps · OBS-008 machine vs semantic
contract under inline/dead/pure motion · OBS-009 Cranelift guard + patch
provider · OBS-010 interpreter masks/JIT transitions, no duplicates · OBS-011
simultaneous activation -> single generation · OBS-012 disable/unload race
safety · OBS-013 failure stages keep old policy · OBS-014 prepare/commit policy
change, no uninit · OBS-015 cross-thread alloc/free/realloc/pool/arena
reconcile · OBS-016 partial coverage declared · OBS-017 collector
recursion/OOM safe · OBS-018 diagnostics without optional packs; CLI stdout
clean · OBS-019 protected path has no loader I/O/alloc/wait · OBS-020
ABI/schema/trust mismatch fails before exec · OBS-021 pointer width / page size
explicit · OBS-022 queued records decodable after generation replacement.
**An unavailable platform or backend yields UNAVAILABLE, never PASS.**

## 3. Reconciliation with the newer docs

| Topic | Plan says | Repo doc says | Resolution |
|---|---|---|---|
| Unload | D5 ends in `unloaded`; D16 "disable != unmap" | XRay V1 status: "Retain tracing code, maps, descriptors and providers until process exit. Logical release never means hot unload." | **Superseded.** Terminal state of the slice is `resident/off`; `unloaded` only via process exit. D16 "disable != unmap" stays true trivially. |
| D15 generation retention | retain until readers quiesce | registry TLDR: quiesce blocks new pins; final pin release retires as one batch | Retention is the registry's job (pins/leases); the slot table only keeps the retired target reachable until the owner says readers quiesced. |
| OFF products | D3 `ERASED` vs `DYNAMIC_READY` | status: "Instrumented-but-disabled and statically-off are distinct products" | Same decision; code name today is `TraceInstrumentationV1 {Off, Dynamic, AlwaysOn}` — `Off` currently conflates ERASED with route-off. |
| Capture shim | D7 | status: "Observer hooks collect bounded records; deferred consumers run aspect behavior. No arbitrary plugin callback in a hidden machine hook." | Same decision. Direct synchronous advice (D7 opt-in) is narrowed by staged plan decision 8 (observer-only; around-advice on separate mechanisms). |
| "One provider" | D11 LLVM XRay = one provider | staged plan §1: Simple facade; Linux LLVM adapter -> Linux Simple-owned -> Windows Simple-owned | Read D11 as "one FACADE; LLVM XRay is the stage-1 provider". |
| LTO/ThinLTO | D11 / OBS-007 up front | staged plan W5/W7 admit LTO incrementally | OBS-007 LTO rows are deferred to W5/W7; never silently fall back. |
| Load-mode names | D4 | none of the newer docs name them; `aspect_pack.spl` implements `lazy_facet` default and refuses `off`/`manual` at startup | Keep D4 names; they are the existing routes. |
| NFR budgets | D3/D4/D14 cost claims | `nfr/aspect_dynload_options.md` offers NFR-A..D budget profiles, still unselected | Numeric budgets wait on the NFR selection; the aspect-off vs disabled startup budget is the one that measures D3. |

## 4. Applied status (2026-11-06)

Legend: **applied** / **partial** / **not-applied**. Evidence paths are relative
to the repo root; `trace/` = `src/lib/common/trace/`.

| ID | Status | Evidence | Proving spec |
|---|---|---|---|
| D1 | partial | Loader + registry reused: `src/lib/common/aspect_pack.spl`, `src/compiler/10.frontend/aspect_registry.spl`; observer config rides `ASPECT_TRACE_OBSERVER_EXT_V1` (`trace/observer_aspect_config_v1.spl:12-27`). No manifest/site-descriptor contract object. | `test/01_unit/lib/aspect_pack_spec.spl` |
| D2 | not-applied | No compact capture plan / site->plan map; only the static match cache `src/compiler/00.common/cache_contract/aspect_match_shard_v1.spl`. | none |
| D3 | partial | `TraceInstrumentationV1 {Off, Dynamic, AlwaysOn}` (`trace/observer_contract_v1.spl:22-25`); `Off` routes with no provider (`trace/observer_build_route_v1.spl:19-20`). No ERASED/DYNAMIC_READY/STATIC_ON build distinction. | `observer_build_route_v1_spec.spl` |
| D4 | partial | `lazy_facet` default route (`aspect_pack.spl:1122`); `off`/`manual` refused at startup (`aspect_pack.spl:53-54`). No log/profile load-mode selection; no explicit resident-only unavailable result. | `aspect_pack_lifecycle_spec.spl` |
| D5 | partial | `TraceSessionStateV1 {Active, Draining, Drained, Faulted}` (`trace/observer_contract_v1.spl:134-138`); `prepare`/`live` in `trace/observer_session_v1.spl:26-85`. No prepared/resident/off states; residency not separated. | `observer_session_v1_spec.spl` |
| D6 | not-applied | No machine/semantic/boundary kinds, no admission failure. | none |
| D7 | partial | Versioned 96-byte LE record (`trace/observer_event_codec_v1.spl:59`); bounded ring with counted overflow (`trace/observer_collector_v1.spl:47`); resident arena channel with cmpxchg record/poll (`src/lib/nogc_sync_mut/trace/observer_native_channel_v1.spl:144-186`). No capture shim, no prepared-site call path; collector is a reference model. | `observer_event_codec_v1_spec.spl`, `observer_collector_v1_spec.spl`, `observer_native_channel_v1_spec.spl` |
| D8 | partial | `PointcutMatchKey` + `negative_root` (`aspect_match_shard_v1.spl:47,158-188`); `aop_match_cache_driver_v1.spl`. No typed matcher IR with read sets, no control-plane algorithm. | `test/01_unit/compiler/aop/aspect_match_shard_v1_spec.spl` |
| D9 | partial | Build ceiling: `AopLogInstrumentationConfig`, `aop_log_should_weave` (`src/compiler/10.frontend/core/aop_log_policy.spl:12-84,135`). No lazy payload region, no impure-payload rejection. | `test/01_unit/compiler/frontend/aop_log_policy_spec.spl` |
| D10 | partial | Negative deps + `.rr v2` identity (`aspect_match_shard_v1.spl:361`). `ObservationSurfaceKey` / `ActivationPlanKey` absent; collector-only no-rebuild not shown. | `aspect_match_shard_v1_spec.spl` |
| D11 | partial | Adapter drives `__xray_patch_function`/`__xray_set_handler` (`src/lib/nogc_sync_mut/trace/xray_llvm_adapter_v1.spl`); `xray-always`/`xray-never` attrs (`src/compiler/70.backend/.../core_codegen.spl:393-408`, `driver_xray_policy.spl`). No LTO/ThinLTO, no capability tuple, no RWX-path rejection on the LLVM path (`xray_native_sled_leaf_v1.spl:23` is the AArch64 Simple patcher only). | `xray_llvm_adapter_v1_spec.spl`, `xray_llvm_attrs_spec.spl`, `xray_policy_spec.spl` |
| D12 | not-applied | No Cranelift guard/data-slot/generation code. | none |
| D13 | not-applied | No per-code-object event masks or host/guest domain split. | none |
| D14 | partial | One facade with level/subsystem/build-ceiling checks (`src/lib/log.spl`); compat module `src/lib/nogc_sync_mut/log.spl:312`. Producer path reads an env var and interns the FORMATTED text on every call (`log.spl:678-686`), ERROR/FATAL go straight to stderr (`log.spl:700-703`); 40-byte ring record (`log.spl:417-438`). No typed versioned record, overflow policy, redaction, or emergency path. | none for layers 2-4 |
| D15 | not-applied | Table sealed RW->RX i.e. executable data (`src/compiler/99.loader/joinpoint_slots.spl:228`); hard-coded `PAGE_SIZE = 4096` (`:95`) and `SLOT_CELL_SIZE = 8` (`:98`); plain `rt_ptr_write_i64` publication (`:207,:287`) and byte-wise dispatch read (`:182-185`); no generation retention. | `test/01_unit/compiler/loader/joinpoint_patchpoint_spec.spl:97` asserts the OLD (executable) design |
| D16 | partial | Receipts and `SIMPLE_GENERATION_NOT_ACTIVE` (`src/lib/nogc_sync_mut/composition/provider_publication_owner_v1.spl:35-112`); `aspect_dynload_publish_next_generation_v1` (`src/lib/common/aspect_dynload_lifecycle_v1.spl`). No 8-step rollback, no cut/drain span policy. | `aspect_dynload_callback_quiescence_spec.spl` |
| D17 | not-applied | No sampling profiler / metric split / finalization status. | none |
| D18 | not-applied | No `allocator_id`, modes, or heap snapshot. | none |
| D19 | partial | `ProviderActivationReceiptV1` (`provider_generation.spl:42`). `SiteDescriptorV1`, `ObserverManifestV1`, `ActivationReceiptV1`, explain API absent. | none |
| D20 | not-applied | No typed application event through the real entrypoint; observer layer is a reference model. | none |
| OBS-001 | not-applied | No ERASED path. | none |
| OBS-002 | partial | Route `Off` resolves with no provider (`observer_build_route_v1.spl:19-20`). | `observer_build_route_v1_spec.spl` |
| OBS-003 | partial | Reference session records to collector and polls (`observer_session_v1.spl:144-195`); not the real activation path. | `observer_session_v1_spec.spl` |
| OBS-004 | not-applied | — | none |
| OBS-005 | not-applied | AOP match cache is static-only. | `aspect_match_shard_v1_spec.spl` (related) |
| OBS-006 | not-applied | — | none |
| OBS-007 | partial | Stage-1 attrs + adapter; no LTO matrix, no live maps (`trace/xray_native_map_format_v1.spl` is format only). Native qualification UNAVAILABLE on this host. | `xray_native_map_format_v1_spec.spl` |
| OBS-008 | not-applied | — | none |
| OBS-009 | not-applied | UNAVAILABLE (no Cranelift provider). | none |
| OBS-010 | not-applied | — | none |
| OBS-011 | not-applied | Adapter retries on ONGOING only; no single-generation rule test. Concurrency qualification: verification-pending on a self-hosted native build. | none |
| OBS-012 | not-applied | Unload is superseded (§3); disable race test absent. | none |
| OBS-013 | partial | Config validated before prepare; `Busy` when live (`observer_session_v1.spl:85`). Staged-failure/old-policy not shown. | `observer_session_v1_spec.spl` |
| OBS-014 | not-applied | — | none |
| OBS-015 | not-applied | — | none |
| OBS-016 | partial | `TraceFailureV1.InstrumentationAbsent` / `UnsupportedSite` (`trace/observer_contract_v1.spl`); no coverage declaration. | `observer_contract_v1_spec.spl` |
| OBS-017 | not-applied | Bounded ring is a precondition only. | none |
| OBS-018 | not-applied | — | none |
| OBS-019 | partial | Native channel imports no allocator/backend/loader (`observer_native_channel_v1.spl`); protected-path property not asserted. | `observer_native_channel_v1_spec.spl` |
| OBS-020 | partial | Schema hash / ext major / `abi_profile` / target / `runtime_identity` validated before use (`trace/observer_native_abi_v1.spl`, `observer_native_map_v1.spl:152`). Trust mismatch not covered. | `observer_native_abi_v1_spec.spl`, `observer_native_map_v1_spec.spl` |
| OBS-021 | not-applied | See D15. `rt_page_size` IS in the seed extern registry (unix + windows, `interpreter_extern/memory.rs:1297`; probed 4096 on this host) — the note in `aspect_pack_io.spl:88` is stale. The C runtime declares it (`src/runtime/runtime.h:362`) but defines it nowhere under `src/runtime/**.c` — native-lane gap. `TargetArch.host()` is hard-coded `X86_64` (`src/lib/common/target.spl:21`). | none |
| OBS-022 | partial | v1/96-byte records decode (`observer_event_codec_v1_spec.spl`); generation replacement not exercised. | `observer_event_codec_v1_spec.spl` |

**Counts:** applied 0 · partial 22 · not-applied 20 (D: 0/12/8; OBS: 0/10/12).

## 5. Implementation order (plan §18, smallest safe first)

1. **D15 / OBS-021** — `joinpoint_slots.spl` as non-executable data: no RX seal, atomic xchg publication + atomic dispatch load (`rt_par_atomic_xchg_i64` / `rt_par_atomic_load_i64`, both SeqCst in the seed), explicit `JoinpointSlotGeometry {pointer_width, page_size}` from the host with checked refusal of any width the atomic primitive cannot cover, retired-target retention gated on a reader pin count. Invert `joinpoint_patchpoint_spec.spl:97` (executable round trip) into a never-executable assertion.
2. **D20 / §18.1 vertical slice** — one typed application event through the log facade with `ERASED` / `DYNAMIC_READY`-OFF / activate -> collector / policy update / disable+drain, specs OBS-001..004 through the real `log.spl` entrypoint; collector stays resident.
3. **D14 producer-path rules** — no formatting/alloc/env read on the producer path when the site is OFF; typed record; overflow policy per stream.
4. D16 transaction + D19 records; then D2/D8/D10 control plane; D11 W-gates per the staged plan; D17/D18 aspects last.

Native-only or concurrency items (OBS-007 LTO rows, OBS-009, OBS-011,
OBS-012) report UNAVAILABLE or verification-pending with the exact stage3 /
native command; they are never marked PASS from a seed run.
