# XRay V1 integration status — 2026-11-03

Status: implementation in progress; not backend qualification or release admission.

The full user-supplied [staged design](simple_xray_staged_implementation_plan_2026-11-03.md) is retained with line-end whitespace normalized. Its historical external evidence is user-supplied; this integration has not independently rerun those workflows or merged draft PR #5962.

## Superseding decisions

- Use a backend-neutral Simple facade across Linux LLVM, Linux Simple-owned, then Windows Simple-owned implementations.
- Retain tracing code, maps, descriptors and providers until process exit. Logical release never means hot unload. Existing general-purpose dynload behavior is unchanged.
- One process capture session; raw edges are baseline. Exact spans and live patching require separate admitted capabilities. Raw folder depth becomes unknown after gaps until resynchronization.
- Windows tracing stays off through stages 1–2. Linux dependencies must be excluded before Windows build evaluation. SimpleOS XRay-OFF remains intact.
- Observer hooks collect bounded records; deferred consumers run aspect behavior. No arbitrary plugin callback in a hidden machine hook.
- Instrumented-but-disabled and statically-off are distinct products. Earlier development-default tracing remains gated on the new target/profile qualification and PERF-01; it is not automatically enabled by this interface patch.

## Current slice

The separate, unlanded interface draft `common.trace.observer_contract_v1` declares the language-level provider port, typed configuration/capabilities, statuses, generation-bearing handle values and canonical event tags. `AspectParamsV1` gains only the named extension constant; its fields, ordinals and defaults are unchanged. No backend or OS dependency is imported and no capability is advertised as implemented.

The proposed 96-byte little-endian event format has an 8-byte header (u16 schema=1, u16 size=96, u16 kind, u16 flags), generation at 8, module instance at 16, u32 function/site at 24/28, context/sequence/timestamp/span at 32/40/48/56, three u64 kind-specific payload slots at 64/72/80 and reserved zero at 88. This is an explicit wire proposal, never the Simple struct layout. Typed allocation/access events remain unsupported; adding their semantics needs explicit capability admission.

W0 is NOT complete: the event/config codecs, generated native ABI caller-buffer validation, golden byte fixtures and actual admitted-runtime compatibility execution remain required. The interface spec is authored, UNRUN. The trait deliberately has no fake backend implementation. Numeric handles are untrusted lookup keys; only a provider-issued resident table entry grants authority.

## PR2 `xray-v1-contract` (2026-11-06)

Re-rooted on `release/1.0.0` (not merged/rebased from the draft branch): `src/lib/common/trace/observer_{contract,config,event_codec,session,collector,native_map,native_abi,build_route,aspect_config}_v1.spl`, `src/lib/nogc_sync_mut/trace/observer_native_channel_v1.spl` (producer release uses the seed+C backed `rt_par_atomic_add_i64(-1)`), and the `simple.trace/observer-v1` constant in `aspect_params.spl`. The 9 draft lib specs now RUN green on the Rust seed (65 examples; the session reference model is a caller-owned value, no module globals). Compile-time intake is ONE gate, `xray_observer_request_check` in `80.driver/driver_xray_policy.spl`, decided once in `CompileContext.create` and stored as `xray_config_error` (the five draft entry-point calls and the `weave_aop` call are gone). It only rejects; it never changes `xray_mode`. Not ported: the `has_errors` early return (Q9, own PR), `observer_llvm_adapter_v1` + hosted-linux fixture (PR4), `mir_observer_site_intent_v1` (superseded), `observer_llvm_host_shim_v1` (PR3).

## PR3 `xray-llvm-attrs` (2026-11-06)

`MirFunction.xray_mode` now reaches LLVM IR as `"function-instrument"="xray-always"` (never-list: `xray-never`, only in instrumented modules; no threshold). `trace.instrumentation` SDN key and the `xray-v1` CompileOptionsHash component (LiveKey pos 49) landed with it. Not yet: `clang_rt.xray` link and the handler shim (PR4), so a `--xray` LLVM binary carries unpatched sleds only.

## Ordered remaining work

1. W0: implement/review codecs, native ABI and golden fixtures; validate with admitted self-hosted tooling; then freeze the contract.
2. W1: bounded collector and generation admission/drain with model-linked native race tests.
3. W2/W3: pinned Linux LLVM shim and real Simple-generated ABI tests; prove Windows-off isolation.
4. W4/W5: Simple-owned emitter/maps/POSIX patch leaves, native Linux qualification and adapter differential tests.
5. W6: independently qualify Windows x64 and ARM64 profiles, including per-binary protection policy association.
6. W7: incrementally admit wider ISA/LTO/live-patch/exact-span modes, never silently fall back.

The earlier visibility/AOP, LSP/MCP, profile and cache/RR requirements remain independent unfinished work. Source-only patches are not passes. Compiler bootstrap Phase 3 is distinct from Windows XRay stage 3.

## Bootstrap coordination

Attempt 7 built Phase 2 and passed its executable sanity but the full verification was stopped by the 20-GiB disk floor. Its outer receipt confirms quiescence; no Phase 3 pass is claimed. The fix-rr branch was rebased to current release with conflict reconciliation; source-dependent checks must use the new source identity. Fetch uses an explicit release refspec because this checkout's configured fetch only tracks release_phase3.

## State on 2026-11-13 (lane `work/spy-xray-20261113`)

Inventory at `3b9e121ecf9` (release/1.0.0). "spy" in the user request is read as
this XRay program (runtime enable/disable of log/profile tracing via aspect
dynload, LLVM-backed and Simple-owned backends); the only other `spy` in `src/`
is the test-double `testing/mock/spy.spl`, unrelated. New code keeps the `xray_*`
naming. The 2026-11-03 "ordered remaining work" above is superseded by the
table below: the Simple-owned Linux backend (plan stage 2) is further along than
the LLVM stage 1, which inverts the earlier sequencing assumption.

### Work packages (plan §16.1) and landing rows (design §F)

| Package / PR | Status | Evidence (file:line, spec) |
| --- | --- | --- |
| W0 freeze V1 facade, statuses, codecs, SDN keys | done (contract not yet declared frozen) | `src/lib/common/trace/observer_contract_v1.spl:27,64,110,155`; `observer_config_v1.spl:29,130`; `observer_event_codec_v1.spl:35,56`; specs `test/01_unit/lib/common/trace/observer_{contract,config,event_codec}_v1_spec.spl` (3+9+6 examples) |
| W1 bounded collector + lifecycle core | done (serial model + lockless ring) | `observer_session_v1.spl:22`, `observer_collector_v1.spl:18`, `src/lib/nogc_sync_mut/trace/observer_native_channel_v1.spl:51,144,157,186`; specs session(2) collector(5) channel(9) |
| W2 / PR4 Linux LLVM adapter + handler shim | partial | control plane `xray_llvm_adapter_v1.spl:82-256` (spec 16 ex., fake leaf); host leaf `xray_llvm_host_leaf_v1.spl:14-47` has NO spec; C shim `src/runtime/xray/xray_llvm_adapter_linux.c:91-155`; **missing:** `clang_rt.xray` link (`80.driver/driver_xray_link.spl:11` declares it out of scope), no `.spl` passes `-fxray-instrument`; no real-binary OUT evidence |
| W3 Windows tracing-off isolation | partial | `core_codegen.spl:559-562` Linux-only attrs; `trace_build_route_v1` refuses non-Linux (`observer_build_route_v1.spl:25`); no command/dependency diff gate |
| W4 / PR5, PR5b native map, emitter, POSIX patch leaves | done (AArch64) | `70.backend/backend/native/xray_sled_emit.spl:142,175,219` (wired `native/mod.spl:84-92,133-138`); `.simple_xray_map` `elf_writer.spl:428`, `elf_writer_serialize.spl:123-198,363`; map codec `xray_native_map_format_v1.spl:154,204` (8 ex.); patch port `src/os/sosix/host/code_patch_adapter.spl:58` (rt_mprotect 60/86); leaf `xray_native_sled_leaf_v1.spl:82,158` (15 ex. + PATCH-02 fault injection); module locate/registration `xray_native_module_v1.spl:134,215,322` (5 ex.); resident runtime `src/runtime/xray/xray_native_runtime_aarch64.c`, registry `xray_native_registry_v1.h:110,163`; e2e `scripts/check/check-xray-native-inprocess-e2e.shs` |
| W4 / PR6 x86-64 SysV | done (object + leaf), execution only on an x86-64 host | `xray_sled_emit.spl:145,178`; `xray_native_trampoline_x86_64_v1.spl:91`; u16 patch `xray_native_sled_leaf_v1.spl:132`; spec `xray_native_sled_leaf_v1_spec.spl:298-322`; `check-xray-native-x86-64-objects.shs`, `check-xray-native-x86-64-inprocess-e2e.shs` |
| W5 native Linux qualification + stage-1 differential | partial | in-process e2e exists for aarch64/x86-64; **missing:** one backend-parameterized suite with identical expectations (this lane, step 2); no LTO subset evidence |
| W6 Windows profiles (PR 8+) | not started in Simple | only native probes under `test/02_integration/xray/*.{S,cpp,ll}`; no COFF map / Win32 leaf |
| W7 live patch (PR7), exact spans, wider ISA | not started | adapter is quiescent-only (`xray_llvm_adapter_v1.spl:40-44`); `TraceConsistencyV1.PairedSpans` rejected (`observer_session_v1_spec.spl`) |
| PR1 `xray-structure` | done | `--xray` `src/app/io/_CliCompile/compile_opt_and_driver.spl:564`; `MirFunction.xray_mode` `50.mir/mir_instruction_graph.spl:313`; policy `driver_xray_policy.spl:49,179`; specs `xray_policy_spec`(17) `xray_mode_transport_spec`(3) `cli_xray_flag_spec`(5) |
| PR2 `xray-v1-contract` | done | see W0/W1; gate `driver_xray_policy.spl:75` (`xray_observer_gate_spec` 13 ex.) |
| PR3 `xray-llvm-attrs` | done | `core_codegen.spl:405,1085`; `xray_llvm_attrs_spec`(17) |
| Data side W5 (sprof data observation) | done, not yet fed by a live hook | `src/lib/common/trace/data/data_observation_aggregator_v1.spl:100,216,251` (its header :23-26 says no compiled hook calls `record()`); `data_sprof_v1.spl:185`; `AdaptiveMap` counters `src/lib/nogc_sync_mut/src/collections/adaptive_map.spl:268-346` never consult a runtime switch and never reach the aggregator |

### Open gaps in the Simple-owned backend (step 3 of this lane)

1. Tail-exit sleds: none (`xray_sled_emit.spl:8-9`). Superseded — not a gap, see "Step 2 result": the native selectors emit no tail calls; the shared profile fold already consumes `TailExit` (`observer_profile_v1.spl:58`) for the LLVM lane.
2. The compile-time observer gate rejects EVERY non-Off route, including
   `backend = Simple` on a `--xray` native build (`driver_xray_policy.spl:79-80`
   -> `UnsupportedProfile`). Aspect-param selection therefore only works through
   the in-process host, never through a compiled request.
3. `xray_llvm_host_leaf_v1.spl` and `observer_aspect_config_v1.spl` have no spec.
4. Linker/trace duplication (fold into shared `src/lib/common/` modules; the
   trace common lib imports `std.common.*` only, the compiler may import std):
   - LE byte read/write: `xray_native_map_format_v1.spl:101,107`,
     `xray_native_module_v1.spl:127`, `xray_sled_emit.spl:260`,
     `observer_native_map_v1.spl:110` vs `linker/elf_inspect.spl:80-94`,
     `linker/_ElfWriter/encoding.spl:94-110`, `linker/reloc_engine.spl:231-312`;
     the intended owner is `src/lib/common/binary_io.spl:701-736`.
   - ELF section-by-name / first PT_LOAD: `xray_native_module_v1.spl:134-166`,
     `xray_sled_emit.spl:271` vs `linker/elf_parser.spl:426,434`,
     `linker/elf_inspect.spl:110,161`, `os/kernel/loader/elf64.spl:138`.
   - AArch64 encoders (STP/LDP/LDR/STR/ADD/SUB): `xray_native_trampoline_aarch64_v1.spl:46-68`
     vs `backend/native/encode_aarch64.spl:296-365`; x86 LE32 `xray_native_trampoline_x86_64_v1.spl:49`
     vs `encode_x86_64.spl:116`.
   - Branch displacement range checks: `observer_native_map_v1.spl:80,91` vs
     `linker/reloc_engine.spl:338,564`; BL/CALL target decode `xray_native_module_v1.spl:168,176`.
   Decision: new `src/lib/common/elf/elf_image_v1.spl` (header + section table +
   section-by-name + first PT_LOAD over an in-memory image, LE via `binary_io`)
   consumed by `xray_native_module_v1`, `xray_sled_emit` and `linker/elf_inspect`
   (names kept, delegating); new `src/lib/common/isa/a64_encode_v1.spl` +
   `x64_encode_v1.spl` (the encoders and displacement checks) consumed by both
   trampoline twins, `observer_native_map_v1` and the backend encoders. The
   other ~680 byte-helper copies in the tree are out of scope.
5. Container switching (step 4): no `AdaptiveMap`/`ContainerPolicy` path consumes
   trace observations; there is no profiling-off early return before counters.

### Test harness (step 2)

The seam both backends share is the `XrayLlvmLeafV1` port
(`xray_llvm_adapter_v1.spl:50`): the LLVM host leaf and `XrayNativeBoundLeafV1`
(`xray_native_sled_leaf_v1.spl:163`) implement it and the same
`XrayLlvmAdapterV1.create_for_backend` drives either. One parameterized spec
runs identical scenarios over both leaves (IN); OUT builds the shared-library
fixture the e2e already uses and asserts on drained events. The Rust seed
honours `@tag:in-development` (explicit-path run prints the honest verdict and
`IN-DEVELOPMENT EXPLICIT`; the suite neutralises it) — cases red today are
tagged, never skipped.

#### Step 2 result (2026-11-13): differential harness landed

- Shared harness `test/fixtures/xray/xray_backend_harness_v1.spl` (`XrayBackendHarnessV1`
  port; LLVM fake leaf, Simple AArch64 and Simple x86-64 sled leaves over a simulated
  code page; function-level `function_on`/`sites_for_function`, fault injection).
- IN suite `test/01_unit/lib/xray/xray_backend_differential_in_spec.spl`: 11 scenarios x 3
  backends = 33 examples, identical bodies. Verdict on the seed:
  `outcome=OK executed=33 passed=33`. Mutation evidence (red on ALL three, then
  restored): exclusive-time fold broken -> 3x `expected 30 to equal 20`;
  `close_admission` skipped on rollback -> 3x `expected false to equal true`.
- Profile mode is a pure fold of the SAME raw-edge stream:
  `src/lib/common/trace/observer_profile_v1.spl` (`trace_profile_fold_v1`).
- OUT suite `test/03_system/xray/xray_backend_differential_out_spec.spl` is
  `@tag:in-development` on this host: the 2026-11-05 seed's `rt_host_dynlib_open`
  returns 0 for every library (bug `seed_rt_host_dynlib_open_returns_zero_2026-11-13.md`)
  and the LLVM lane has no Simple-compiled binary (PR4 link). The host fixture now
  prints `timestamps_nonzero=` so timing presence is asserted the same way on both.
- Tail-exit sleds are NOT a gap: the native selectors emit no tail calls
  (`xray_sled_emit.spl:8-9`), so there is no tail-exit site to instrument.
- Bug: `use test.fixtures.*` is unresolved from specs deeper than depth 4
  (`test_fixtures_import_unresolved_below_depth4_2026-11-13.md`); the IN spec sits at depth 4.

#### Step 3 result (2026-11-13): shared ELF / ISA / LE modules

- `src/lib/common/binary_io.spl` gains `bytes_read_le_at` / `bytes_push_le` (width 1..8,
  direct indexing, no 0 sentinel); `src/lib/common/elf/elf_image_v1.spl` (ELF64 LE header,
  section table, section-by-name, section bytes, first PT_LOAD vaddr; None on malformed);
  `src/lib/common/isa/a64_encode_v1.spl` (NOP, B/BL imm26 + word/byte range, STP/LDP X/Q,
  STR/LDR X, ADD/SUB imm12, linker imm26) and `x64_encode_v1.spl` (imm32 LE, rel32 range).
- Trace / XRay consumers now delegate instead of carrying private copies:
  `xray_native_map_format_v1` (LE put/get), `observer_native_map_v1` (word append, branch
  ranges, BL), both trampoline twins (all encoders except MRS/MSR), `xray_native_module_v1`
  (section lookup, first PT_LOAD, u32 read), `xray_sled_emit` (object section lookup).
  Golden bytes unchanged: every existing xray spec is green with identical counts.
- Mutation: `a64_bl_v1` opcode 0x94 -> 0x95 turns both the AArch64 trampoline twin spec and
  `observer_native_map_v1_spec` red (1 failure each) — the twins really share one encoder.

#### Step 4 result (2026-11-13): container profiling switch + trace data port

- `AdaptiveMap` / `AdaptiveSet` carry a `profiling` bool (`set_profiling`,
  `profiling_enabled`). Off: `get` / `contains_key` do one bool test, the ordered-key
  guard and the storage lookup; `put` / `remove` skip the peak-size counter and the capture
  note. Default stays `true` (unchanged behaviour for every existing caller).
- `src/lib/common/trace/data/data_observation_sink_v1.spl`: `DataObservationSinkV1` port,
  `data_observation_profiling_enabled_v1(TraceConfigV1?)` (Off/absent -> false) and
  `data_observation_profiling_from_aspect_v1(AspectParamsV1)` (the `simple.trace/observer-v1`
  extension; malformed fails closed to off); `DataObservationAggregatorSinkV1` bridge.
- `src/lib/nogc_sync_mut/src/collections/adaptive_trace_observation.spl`: one observation ->
  lookup / size / representation-transition records, publish through the sink (0 records and
  no sink call when disabled), and drained records -> `AdaptiveSetWorkloadProfile` that
  `apply_workload_profile` consumes.
- Spec `test/01_unit/lib/collections/adaptive_trace_observation_v1_spec.spl` 6/6; 1/6 with the
  `adaptive_map`/`adaptive_set` change reverted (red -> green).
- Pre-existing, unrelated reds in sibling adaptive specs on the Rust seed (identical with and
  without this change): `unknown extern function: spl_ordered_key_cmp` /
  `spl_collection_capture_note_size` / `spl_collection_capture_begin`, `Dict.capacity`.
- NOT yet wired: no production path calls `set_profiling` from the XRay adapter's runtime
  enable/disable; `data_observation_profiling_from_aspect_v1` has no live caller yet.

#### Step 3b (2026-11-13): the linker and the x86-64 backend consume the shared modules

- `70.backend/linker/elf_inspect.spl` `elf_read_u{16,32,64}_le` delegate to
  `elf_image_u*_le_v1` (its ELF32 branches stay local; `elf_image_v1` is ELF64-only).
- `70.backend/linker/reloc_engine.spl` R_AARCH64_CALL26/JUMP26 range + imm26 use
  `a64_branch26_bytes_in_range_v1` / `a64_imm26_from_bytes_v1` (equivalent after the
  preceding 4-byte alignment check; the spec pins 2^27-4 accept, 2^27 reject, -2^27 accept).
- `70.backend/backend/native/encode_x86_64.spl` `emit_i32` delegates to
  `x64_push_imm32_le_v1` (unrolled, no per-call list).
- Before/after on 10 linker + backend specs: identical verdicts and identical failure set
  (pre-existing: elf_parser 1, sym_resolver 1, elf_exec_writer 13). Mutations in the shared
  modules turn the consumers red: imm26 mask -> reloc_engine 121/122; ELF u16 width ->
  elf_header_phnum 1/2; imm32 top byte -> x86_negative_imm64 1/9.
- Remaining duplication (not folded): `linker/elf_parser.spl:426,434` section lookup,
  `linker/_ElfWriter/encoding.spl`, `encode_aarch64.spl` STP/LDP/ADD encoders, kernel loader.

#### Step 4b (2026-11-13): container switch follows the XRay enable/disable

- `data_observation_profiling_while_v1(config, controller_active)`: on only between
  `start` and `request_stop` (adapter state Active) under a non-Off aspect config.
- IN differential suite gains "container switching follows runtime enable/disable" for all
  three backends (36 examples, was 33): off before start, counters + generation-stamped
  records while Active, frozen after stop, Off aspect / absent extension never turn it on.
  Red (function missing) 33/36 -> green 36/36; mutation dropping `controller_active` -> 33/36.
- Still open: no compiled program calls `set_profiling` from its in-process XRay host yet
  (the harness and specs do); the OUT lane for containers waits on a backed binary
  (`spl_ordered_key_cmp`, `spl_collection_capture_*` are not in the seed).

#### Step 3c (2026-11-13): ELF read-path timing — correction and fix

Correction: `linker/elf_inspect.spl` is NOT diagnostic-only. Its `elf_read_u{16,32,64}_le`
are imported by the production object parser `linker/elf_parser.spl:7-10` (symbols,
relocations, ARM REL addends, section lookup) and by `linker/elf/shared_object.spl:8-10`;
`elf_parse_header`/`elf_parse_sections` feed every `elf_parse_object` caller
(`elf_static_link`, `section_gc`, `archive_closure`, `tls_relax`, `smf_group_object_adapter`, ...).

Workload: `test/05_perf/compiler_perf_baseline/elf_inspect_read_probe.spl` over a 1,889,856-byte
clang `-O1 -g` object of `src/runtime/runtime_native.c`; `parse` = 5 x `elf_parse_object`,
`read` = one u16+u32+u64 sweep at every 8th offset. Binary: Rust seed
`bootstrap.generations/8ea37491…/simple` (sha256 `df9dfb057afb7b8f…`, 119,570,696 B,
2026-11-05 18:12), interpreter lane (the probe's JIT attempt falls back on
`Cannot infer field type: ElfObject.symbols`), 4G scope, 3 alternating runs each, load 7-20.

| variant | parse wall s | read wall s | max RSS KiB |
| --- | --- | --- | --- |
| old (`b795b3f4a26~1`, unrolled local readers) | 10.14 / 10.09 / 9.83 ; 11.60 / 11.32 / 10.59 | 8.90 / 8.92 / 8.90 ; 9.67 / 9.37 / 10.39 | 255,688-271,968 |
| `b795b3f4a26` (delegate -> `bytes_read_le_at` loop) | 14.97 / 15.33 / 15.02 | 19.12 / 19.38 / 19.61 | 273,724-274,064 |
| fixed (shared readers unrolled) | 9.03 / 9.31 / 9.34 | 9.79 / 9.48 / 9.64 | 256,544-262,316 |

`b795b3f4a26` regressed parse 1.5x and raw reads 2.2x (+2 MB RSS). Fixed by unrolling
`elf_image_u{16,32,64}_le_v1` in the shared module (the linker keeps delegating; one extra
call layer, no loop): parse and reads back at the old level, RSS within run noise.
Pinned by a new `elf_image_v1_spec` example with 8 distinct byte lanes (a `<< 56` -> `<< 48`
mutation of the u64 top lane survived the old spec and now fails 12/13).

Other `b795b3f4a26`/`aba2a5f0a3e` sites, same seed and scope:
- `reloc_engine` CALL26/JUMP26 delegation: 200,000 `reloc_apply_aarch64` CALL26 calls,
  old 3.91 / 3.93 / 5.19 s vs delegated 6.22 / 6.12 / 8.22 s (1.6x), RSS equal. Reverted to
  the inline check (3.87 / 3.83 s after revert); `a64_branch26_bytes_in_range_v1` and
  `a64_imm26_from_bytes_v1` lost their only consumer and were removed with their examples.
- `encode_x86_64.emit_i32` -> `x64_push_imm32_le_v1` (one call + 4 pushes replacing 4 helper
  calls with a branch + division each): 1,000,000 calls, 5 alternating pairs at load ~20,
  old 3.02 / 3.61 / 2.53 / 3.63 / 4.25 s vs new 2.07 / 4.13 / 4.62 / 2.11 / 2.11 s (median
  3.61 vs 2.11). No regression signal; kept.

#### Step 4c (2026-11-13, branch `work/spy-xray-2-20261113`): host policy + construction value

- `src/lib/nogc_sync_mut/trace/xray_data_profiling_v1.spl` `XrayDataProfilingV1.from_aspect`:
  absent observer extension -> containers profile as before (initial and after = true);
  malformed or `off` -> false; `always_on` -> true; `dynamic` -> false at construction, then
  `after(adapter.state_code())` is true only while Active. Spec 6/6 (red: module missing);
  mutation absent -> Never: 4/6 and IN 33/36.
- `AdaptiveMap.with_profiling(profile, enabled)` / `AdaptiveSet.with_profiling` construct with
  the policy's `initial()`; the per-instance bool stays the only per-operation cost.
- The in-process host fixture (`test/fixtures/xray/xray_native_inprocess_host.spl`) now builds a
  container per session with `initial()`, flips it right after `start` and right after
  `request_stop`, and prints `E2E <s> container ...`; `xr_session_ok` checks it (selftest has
  four new rejecting mutations). The lane remains OUT-blocked by the seed dynlib bug, so
  "a compiled program flips set_profiling" is wired but not yet observed on a real module.
- IN suite scenario now goes through the policy (36/36).

#### Step 3d (2026-11-13): linker folds, branch `work/spy-xray-2-20261113`

- `_ElfWriter/encoding.spl` `write_u{16,32,64}_le` and `std.common.isa.x64_encode_v1`
  `x64_push_imm32_le_v1` are now ONE body each in `std.common.binary_io`
  (`bytes_i64_push_u{16,32,64}_le`), re-exported with `export use ... as ...` so no caller
  gains a call layer. 64 x (u16+u32+u64) writes x 20,000 through `elf_writer`: old
  51.61 / 51.46 / 52.74 s vs shared 47.91 / 47.81 / 48.43 s (RSS 233-259 MB both). Same
  failure set on 9 writer/encoder specs; mutating the shared writers turns
  `elf_writer_spec` (17/18), `x86_negative_imm64` (1/9) and `x64_encode_v1` (1/2) red.
- `linker/elf_parser.spl` is NOT folded further: it already reads every field through the
  shared readers (`elf_inspect` -> `elf_image_u*_le_v1`, Step 3c), and its section-table
  walk carries ELF32 support that `elf_image_v1` deliberately lacks; routing its ELF64 half
  through `elf_image_sections_v1` would add an intermediate list per parse on the path
  Step 3c measured.
- `backend/native/encode_aarch64.spl`: `emit_u32_le` is the shared `bytes_i64_push_u32_le`
  (aliased import; the local mod/div body is gone); ADD/SUB imm12, LDR/STR unsigned offset
  and the offset (non-writeback) STP/LDP forms call `std.common.isa.a64_encode_v1`. Kept
  local: the pre/post-indexed writeback pairs (no shared form) and the ADD relocation
  placeholder (its literal text is pinned by `global_addr_aarch64_riscv64_contract_spec`).
  New `aarch64_shared_encoder_parity_spec` (3/3 on old and new encoder; mutations of the
  shared ADD/SUB/LDR/STR encoders -> 1/3, LDP -> 2/3). 7 instructions x 20,000 through
  `encode_inst_aarch64`: old 12.07 / 12.16 / 12.28 s vs new 12.07 / 12.23 / 12.28 s, RSS
  ~142 MB both. Same verdicts on the 9 AArch64 encoder specs (incl. the pre-existing 3
  failures of `global_addr_aarch64_riscv64_contract_spec`).
- `a64_b_v1` / `a64_nop_v1` deleted: the backend emits B/BL/NOP as constant placeholders
  that relocations patch, so a call buys nothing and they had no other consumer.
- Kernel loader (`src/os/kernel/loader/elf64.spl`) keeps its ELF64 readers. It could import
  `std.common` (sibling loader files do), but its readers come from the kernel-owned
  `os.kernel.loader.byte_utils` shared by the whole loader, and any loader change needs the
  real-firmware QEMU/board boot evidence of `.claude/rules/board-runnable.md`, which this
  lane does not produce. Recorded as remaining duplication, not folded.

#### Step 3e (2026-11-13): shared PE/COFF reader (stage-3 groundwork)

- New `src/lib/common/pe/pe_image_v1.spl`: bounds-checked LE readers (-1 when truncated, the
  linker's contract), name decoder, bigobj probe, classic/bigobj COFF header record, 40-byte
  section header record, and a linked PE32+ image (machine, image base, section alignment,
  size, exception directory, section table, section-by-name, RVA -> file offset). Spec
  `test/01_unit/lib/pe/pe_image_v1_spec.spl` 7/7; its image fixture is written by the
  linker's own `pe_write_amd64_console`.
- `linker/coff/coff_object.spl` takes header layout (`pe_coff_header_v1`), section headers
  (`pe_section_header_v1`) and `coff_is_bigobj` (aliased re-export) from it; 3 private size
  constants deleted. Mutating the shared section-header / header readers -> `coff_object_spec`
  15/21 and 11/21. 15 COFF/PE linker specs: identical failure set before/after.
- Timing (626,353-byte clang `x86_64-pc-windows-msvc` object, 12 x `coff_parse_object`):
  old 15.89 / 15.90 / 15.47 / 15.40 / 15.90 s; first fold with a record per relocation
  ~1.3x and imported readers +8% (17.1-17.3 s) -> reverted both: the relocation loop reads
  fields directly and the five field readers stay module-local. Final: 15.72 / 16.28 s.
  Filed `doc/08_tracking/bug/seed_cross_module_call_overhead_2026-11-13.md`.
- Not folded (remaining PE duplication): `linker/pe_inspect.spl`, `linker/pe_parser.spl`,
  `std.common.pe_coff_header` (image gates), `src/lib/pe_coff_header.spl` (stub).

### Stage 3 (Windows x64, Simple-owned) — 2026-11-13

#### W1: trampoline, unwind records, resident runtime TU
- `src/lib/common/trace/xray_native_trampoline_win64_v1.spl`: Simple twin of
  `__simple_xray_trampoline_win64_v1` (354 bytes; bounded AVX profile: rbp + rax rcx rdx
  r8-r11, ymm0-15 in full, MXCSR, RFLAGS in-frame; 32-byte shadow space; rsp 16-aligned
  and DF clear at the CALL; ecx = id, rdx = sled return; canonical `lea rsp,[rbp]` epilog),
  UNWIND_INFO / RUNTIME_FUNCTION encoders, and the entry-sled admission rule (no prolog
  unwind code inside the 13-byte sled; chained / non-v1 info refused).
- `src/runtime/xray/xray_native_runtime_win64.c`: the resident TU (same .seh-annotated asm,
  sled leaf, registry with `__ImageBase` + RVA text_base and `__declspec(dllexport)` entry
  points). `xray_native_registry_v1.h` gained two overridable macros (`SIMPLE_XRAY_API`,
  `XMAP_TEXT_BASE`); the Linux expansions are unchanged.
- Evidence: spec 9/9 with goldens from clang 23 `x86_64-pc-windows-msvc` (text and .xdata);
  `scripts/check/check-xray-native-win64-objects.shs --simple <seed>` PASS (trampoline
  bytes and assembler UNWIND_INFO == twin); mutating the twin (cld -> nop) -> script FAIL and
  spec 8/9. Wired as `local-xray-native-win64-objects` in `config/check/must_check_gates.sdn`.
- Patching on Windows reuses the existing leaf and SOSIX port: `rt_mprotect` is
  VirtualProtect + FlushInstructionCache with rollback (`platform_win.h:504-520`), one
  aligned u16 activation-word store, quiescent only.

#### W2: Windows map profile, PE locator, 4th IN column
- `xray_native_map_format_v1`: `XRAY_MAP_ABI_X86_64_WIN64_V1 = 3` admitted on x86-64 rows (text_base
  = .text RVA), refused under AArch64; `.sxray` is the PE section name. Map spec 10/10 (red
  9/10 with the old validator).
- `src/lib/common/trace/xray_native_pe_locate_v1.spl` (pure): PE file bytes + HMODULE base ->
  RVA manifest (`x86_64-pc-windows-msvc`, `simple-x86_64-win64-sled-v1`), reconstructed image,
  CALL targets decoded per sled; refuses missing `.sxray` (InstrumentationAbsent), writable /
  executable map section, non-Windows profile, 64-bit text_base, tampered CALL, unaligned base.
  Spec 5/5; mutation of the CALL decode -> 4/5.
- IN differential suite: 4th column `simple-win64` built from a PE image written by the
  linker's own PE writer (`test/fixtures/xray/xray_win64_pe_fixture_v1.spl`) -> locator ->
  validator -> `XrayNativeSledLeafV1` over the simulated page: 12/12 identical scenarios,
  48/48 total. Mutating the locator's CALL target -> 36/48 (the whole win64 column red).
- NOT changed (coordinator decision): the W3 build route still refuses every Windows target.
  Admitting `x86_64-pc-windows-msvc` + backend Simple needs the native backend's COFF sled
  emission (sleds, `.sxray` with ADDR32NB text_base, `.pdata` offsets past the entry sled)
  and touches `observer_build_route_v1.spl`, `driver_xray_policy.spl:85-92`,
  `observer_build_route_v1_spec.spl` and `xray_observer_gate_spec.spl` in one reviewed change.

#### W3: OUT suite, Windows column
- `test/03_system/xray/xray_backend_differential_out_spec.spl` (still `@tag:in-development`)
  gains `simple-win64`: the static half (`check-xray-native-win64-objects.shs`) PASSes on this
  Linux host; the in-process half fails with an explicit BLOCKED message naming the missing
  lane `scripts/check/check-xray-native-win64-inprocess-e2e.shs` (Windows x64 host + the
  backend's COFF sled emitter), never a skip. Explicit-path run 2026-11-13 (seed, lanes capped
  150 s, 8G scope): llvm PASS, simple FAIL (seed `rt_host_dynlib_open` bug), win64 static PASS,
  win64 in-process BLOCKED -> `passed=2 failed=2`, `IN-DEVELOPMENT EXPLICIT`.
- Notes: the locator's 64-bit-text_base refusal is defence in depth (a wide value is also
  refused by section containment), mirroring the runtime's uint32 truncation. The twin dump
  prints twice under the seed (engine demotion re-runs `main`); the objects check reads the
  first line — filed `doc/08_tracking/bug/seed_engine_demotion_reruns_main_side_effects_2026-11-13.md`.

#### Review round 1 fixes (2026-11-13)
- Aliased re-exports removed (`export use m.{a as b}` did not resolve on the reviewer's pinned
  seed through `elf_writer`'s glob re-export; bug `seed_aliased_reexport_unresolved_2026-11-13`).
  Thin local wrappers were measured on the ELF writer probe: 71.78 / 73.73 s vs release 52.24 /
  50.95 s (1.4x) — so the hot emitters keep module-local bodies instead: `_ElfWriter/encoding.spl`
  and `encode_x86_64.spl` are back to release content, `encode_aarch64.spl` keeps its local
  `emit_u32_le`, `x64_push_imm32_le_v1` has its own body again (cold: XRay twins only), and the
  `bytes_i64_push_u{16,32,64}_le` helpers are deleted. Step 3d's writer/x64 fold is withdrawn.
  `coff_is_bigobj` is a local wrapper (once per object). `a64_new_encode_context` /
  `encode_inst_aarch64` are `pub` so the encoder specs run on strict binaries.
- Windows trampoline: a sled sits where rsp is 8 mod 16, so the trampoline entry is 0 mod 16;
  the old 8 pushes + 0x238 left rsp 8 mod 16 at the handler CALL. Now push rbp; pushfq (RFLAGS
  saved before the first flag-writing `sub`); 7 volatile GPRs; mov rbp,rsp; sub 0x238 -> 640
  bytes, 0 mod 16 at the CALL. 340 bytes, prolog 23, 12 unwind slots (ALLOC_SMALL for pushfq),
  epilog `lea; pops; popfq; pop rbp; ret`. New spec example decodes the prolog bytes and asserts
  the alignment (old twin: 6/10, new: 10/10); clang byte/unwind parity check PASS. Windows
  `-Wall -Wextra` build has no warnings (unused `field` fixed in the Windows XMAP_TEXT_BASE).
