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

1. Tail-exit sleds: none (`xray_sled_emit.spl:8-9`); EMIT-01 tail-call row is unmet.
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
