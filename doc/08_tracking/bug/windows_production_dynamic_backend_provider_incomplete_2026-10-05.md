# Windows production dynamic backend providers are incomplete

Status: OPEN (P1). Confirmed source-level gaps; no production repair or native provider
validation performed in this audit. Blocks the requested same-frontend,
dynamically selected LLVM/Cranelift full-bootstrap claim.

Audited source: `release_temp` base `cc05d7f451467657a6cf5fc464dfd09d8239ef9f`
plus unrelated ABI-receipt repair `79dbe072fc3`. Active frozen source `916be6`
and its bootstrap processes/caches were not modified. This is a production
backend-provider issue, not the hosted runtime's ordinary library primitives.

## Confirmed gaps

1. **Windows consumer invocation is unsupported.**
   `src/runtime/runtime_backend_plugin.c:149` implements
   `spl_backend_plugin_run_v1`; its `_WIN32` branch at 161 returns status 102.
   Batch open at 192 returns -102 on Windows; batch compile at 224 and finalize
   at 247 likewise return 102. Loading a DLL and resolving its symbol cannot
   make these operations execute. The Rust interpreter extern at
   `src/compiler_rust/compiler/src/interpreter_extern/wsffi.rs:254` also returns
   status 102 on non-Unix; it is not an alternate Windows implementation.
2. **No production provider entry definition/build recipe was found.**
   Bounded searches of owned `src`, `test`, `scripts`, and `tools`, excluding
   vendor and target trees, found `simple_backend_plugin_v1(...)` definitions
   only in `test/fixtures/backend_plugin/dynamic_loader_provider_v1.c` and
   `test/01_unit/compiler/backend_plugin/fixtures/backend_plugin_v1_fixture.c`.
   The former returns integer 1 to test symbol presence; it is not a descriptor
   provider. The latter returns fixture text `module-ok`/`object-ok`, not real
   LLVM/Cranelift object code. Existing build scripts produce fixture `.so`
   files, not production backend DLLs. The header contains only a declaration.
3. **Request transport discards compilation configuration.**
   `src/compiler/70.backend/backend_plugin/transport.spl:127`,
   `backend_plugin_request_encode_v1`, emits only ABI u32, role u32 and capability
   mask u64. Runtime request construction at `runtime_backend_plugin.c:116`
   and 211 zero-initializes backend name, target, CPU, features, optimization,
   and MIR ABI digest. These fields exist in the C request but never arrive.
4. **Foreign descriptor semantic admission is incomplete.**
   `backend_plugin/loader.spl:40`, `load_dynamic_backend_v1`, constructs its
   local descriptor from the request and staged-file hash (line 54), then
   makes a receipt from that projection. Unlike the built-in path, it does not
   admit the actual foreign metadata through `admit_backend_plugin`.
   Runtime descriptor checks at lines 77 and 104 check ABI, structure sizes,
   and required function pointers, but not foreign provider version, MIR
   digest, role mask, target list or capabilities. A request-derived receipt
   does not prove the provider supports that request.
5. **MIR transport is not full-module semantics.**
   `src/compiler/50.mir/mir_serialization.spl:13`, `serialize_mir_module`,
   explicitly emits a functions-only compatibility JSON shape. The real
   `MirModule` at `mir_instruction_graph.spl:443` also has statics, constants,
   type definitions, and external layout traces. Dynamic transport uses this
   serializer at `transport.spl:196` and 208. A bounded named-decoder search
   found no matching production MIR module deserializer; absence of that
   search result is not a claim that every differently named decoder was
   exhaustively excluded. Full bootstrap cannot silently drop those fields.

## Existing callable ABI and ownership

Normative header: `src/compiler/70.backend/backend_plugin/abi/simple_backend_plugin_v1.h`.
Entry: exported `const simple_backend_descriptor_v1 *simple_backend_plugin_v1(void)`.
ABI and bridge versions are 1. Structures use fixed u32/u64 fields plus
pointer/length slices; foreign `struct_size` is a byte count checked against
native `sizeof`, distinct from the common Simple model's logical minimum 9.

- Request: ABI/size/role/reserved, backend/target/CPU/features/optimization/MIR
  digest slices, required-capability u64 mask.
- Descriptor: ABI/size, provider identity/version/build/MIR digest slices,
  role/capability masks, target wire slice, borrowed immutable vtable pointer.
- Vtable: `open_session(request*, session*)`, `compile_module(session, MIR,
  result*)`, `finalize_object(session,result*)`, `diagnostics(session,buffer*)`,
  `close_session(session)`, `release_buffer(session,buffer)`.
- Provider output `(data,size,owner_token)` remains provider-owned until copied
  and released exactly once. Final object result kind is 2. Adapter validates
  object magic and publishes through private same-parent staging.
- Transport envelope SBP1 is 32 bytes plus payload and diagnostic; admitted
  provider handle packet SBH1 is 16 bytes. The lease pins one loaded mapping,
  hashes private staged bytes before/after loading, and must outlive operations,
  buffers and sessions. Do not replace it with repeated path loads.

The C vtable has no execute slot although the higher-level model includes JIT
execution. The requested AOT bootstrap can be implemented first with honest
CompilerAot/ObjectEmit capabilities; claiming JIT support needs another ABI step.

`bootstrap_main.spl:235`, 396, 543 and
`bootstrap_native_output_args.spl:20` expose/project `--backend-plugin`.
`load_backend` chooses dynamic only when `has_plugin_path` is true. CLI
`--mode dynload` controls artifact/aspect packaging and is not evidence that a
backend provider was selected or called (`compile_targets.spl:262` documents
its separate incomplete automatic aspect-pack path).

## Smallest truthful integration scope

This cannot be completed by adding a DLL filename or enabling a flag.

1. Implement the Windows typed transport in its existing runtime owner using
   the already-admitted handle and Windows symbol APIs; preserve pinning,
   copied-buffer ownership, failure cleanup and diagnostics for single/batch.
2. Version a complete bounded request/MIR wire contract and a corresponding
   provider decoder. Preserve all backend-relevant module fields and numeric,
   layout, target, CPU/features and optimization semantics. Reject unsupported
   schema/version explicitly instead of truncating to functions.
3. Read and admit the real provider descriptor before session open; derive
   receipts from admitted actual metadata plus immutable binary identity.
   Require ABI/MIR/version/role/target/capability rejection before provider work.
4. Build real LLVM and Cranelift DLLs exporting the header contract. Reuse
   existing Pure-Simple backend logic via an explicit owned adapter, with only
   necessary FFI glue: LLVM `backend/llvm_codegen_adapter.spl` and Cranelift
   `backend/cranelift_codegen_adapter.spl`; preserve target context from
   `backend_plugin/builtin_adapter.spl`. Do not move compiler implementation to
   C/Rust or pass Simple heap graphs across the foreign allocator boundary.
5. Add immutable build manifests and bootstrap option propagation: one exact
   frontend hash must compile with either exact provider DLL, carrying their
   identity through Phase 2/3/4. Qualify the selected provider and fail if absent;
   no built-in fallback or static-symbol proof substitutes for this.

## Existing requirements and tests

Existing requirements are not new hypothetical scope:
`doc/02_requirements/feature/versioned_codegen_backend_plugin.md`, especially
REQ-001/002/006/007/008/009, already require common static/dynamic contract,
actual descriptor admission, no substitution and provenance. NFR-002 allows
20 ms warm dynamic admission; NFR-003 forbids scans/subprocesses in selection;
NFR-004 requires one retained provider session. Architecture/detail design at
the same stem already describes the ABI and ownership. Their status text is
partly stale relative to current consumer adapter implementation and must be
updated from actual evidence, not treated as completed implementation.

Existing coverage (not run by this audit):

- `test/01_unit/compiler/backend_plugin/backend_plugin_v1_abi_contract_test.shs`
  and `backend_plugin_v1_native_bridge_test.shs`: Unix C fixture lifecycle,
  malformed ABI/size, operation failures and release counts.
- `dynamic_loader_spec.spl`, `dynamic_provider_content_identity_spec.spl`,
  `dynamic_object_path_transport_spec.spl`: lease, identity and publication.
- `test/01_unit/compiler/driver/backend_plugin_cli_propagation_contract_test.shs`.
- `test/03_system/app/compiler/feature/versioned_codegen_backend_plugin_spec.spl`
  identifies itself as a source-contract spec, not real codegen-provider proof.

Required added evidence: Windows real provider load/export/descriptor rejection,
configuration and complete MIR roundtrip parity (statics/constants/types/layout),
actual linked and executed arithmetic/branch/call/array/layout/float programs,
wrong-provider/no-fallback tests, single/batch failure diagnostics, exactly-once
buffer/session/library cleanup, changed-provider cache miss and unchanged hit,
and full bootstrap with the same frontend and both provider identities. Pair
startup/request latency with peak and steady RSS; distinguish diagnostic runs
from canonical Phase 4 admission. Existing fixture PASS cannot close these gaps.
