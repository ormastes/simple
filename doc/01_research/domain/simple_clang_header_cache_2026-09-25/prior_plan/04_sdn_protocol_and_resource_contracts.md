# Report 4 — SDN protocol, binary resources, and provider contracts

**Date:** 2026-09-25  
**Status:** Proposed schema contract, not an implemented protocol. The accompanying `.sdn.example` files are design templates, not parser-validated production configuration.

## 1. Protocol decision

SDN is the native representation for job submission, worker registration, group configuration, actions, resource metadata, policy, status events, and receipts. Bulk source/resource/object bytes remain binary. A fixed-layout local ring is an optional binary transport over the same typed message semantics, not a competing control protocol.

GitHub's own workflow YAML and Git's `.gitmodules` syntax remain boundary adapters because those tools require their formats. Neither becomes the internal build protocol. A future REAPI bridge may translate to its external binary protocol, but it is optional and must not force protobuf/gRPC into the native scheduler or change the authoritative Simple identities.

Within a group process use typed function calls and futures; do not serialize every resource lookup into SDN. Across processes default to framed SDN over an authenticated local channel. Optimize to a binary ring only when profiling shows that framing/parsing matters. Across hosts use authenticated encrypted connections with framed SDN messages and bounded separate binary streams.

## 2. Envelope and compatibility

Every message contains protocol major/minor, schema ID, message kind, request/correlation ID, tenant/repository scope, and payload. Job/action/attempt/fence fields appear where applicable. Major incompatibility is rejected; unknown mandatory fields fail. Minor extensions need an explicit capability rule. Do not silently ignore an isolation or trust field that the peer does not understand.

Bound frame length, nesting, collections, string sizes, decompression output, number of referenced blobs, and total materialization. Validate UTF-8 before parsing text; binary data never passes through a `text` API. Check a declared digest over the actual uncompressed payload bytes. Malformed input produces a structured rejection and must not crash the worker/control process.

Transport authentication identifies the peer, while authorization checks its job/resource scope. A digest identifies content; it is not permission to read it. Public, organization-private, local developer, untrusted PR, and release namespaces must enforce distinct access/publication rules. Do not allow a client to select a more-trusted namespace merely by supplying its name.

## 3. Schema families

| Family | Required meaning |
|---|---|
| `SnapshotManifest` | Exact source tree; generated inputs; file modes/symlinks; dependency pins and snapshot identity. |
| `ToolchainManifest` | Executable, runtime, libraries, sysroot/SDK, resource directory, plugins, provider schema, host compatibility. |
| `InputManifest` | Authoritative resolved read closure, producer artifacts, negative probes, configuration, completeness evidence. |
| `ActionSpec` | Computation kind, exact tool/input roots, ordered arguments, relevant environment/target and declared outputs. |
| `AttemptSpec` | Job/action reference, attempt ID, current epoch/fence, allocation, execution mode, deadline, replay policy. |
| `ResourceDescriptor` | Provider/kind/format/version, digest/length, target/context key, access scope, mapping/stream capability. |
| `ResourceLease` | Object generation, holder identity/epoch, pin mode, lifetime and revocation/quiescence contract. |
| `ActionResultCandidate` | Outputs/logs/diagnostics, input-closure evidence, producer attempt, exit/outcome, no self-admission. |
| `AcceptedResult` | Broker-validated immutable manifest and current publication evidence. |
| `GateReceipt` | Snapshot/base/policy, expected/observed work, exact validation environment, outcomes, issuer/signature. |
| `NodeCapabilities` | Execution OS/arch, sandbox/provider ABI, capacities, native/emulated devices, license and trust constraints. |

Canonical identity is derived from typed semantic fields through existing Simple canonical encoders. Preserve the current key format unless a reviewed versioned migration replaces it. SDN text rendering and optimized binary transport must produce the same typed semantics. The inspected action-key code already distinguishes ordered resolver probes from set-like fields. [R05]

## 4. Example SDN authoring shape

The following uses SDN's table-oriented style already present in the gate registry. Field names and schemas are proposed. Placeholder digests intentionally cannot be admitted as real identities. Validate exact parser syntax and normalize it during W0. [R10]

```sdn
protocol |major, minor, schema, example_only|
    1, 0, "simple.build.action.v1", true

action |id, kind, input_manifest, toolchain, execution_profile, target_profile|
    "ACTION_DIGEST", "compile", "INPUT_MANIFEST_DIGEST", "TOOLCHAIN_DIGEST", "linux-x86_64", "riscv64-simpleos"

arguments |position, value|
    0, "compile"
    1, "src/example.spl"

outputs |path, kind|
    "out/example.o", "file"

attempt |id, fence, preferred_mode, cpu_tokens, memory_mib|
    "ATTEMPT_ID", 1, "qualified_group_thread", 1, 1024
```

The planner resolves profile names and version aliases into full immutable manifests; strings such as `linux-x86_64` alone are insufficient ABI/toolchain identity. Scheduling hints and semantically relevant inputs remain separately classified. A binary local descriptor references a prevalidated ActionSpec; it does not omit validation by replacing a large manifest with an untrusted integer.

## 5. Group and startup resource configuration

```sdn
group |id, provider, toolchain, trust_class, max_active_actions, example_only|
    "simple-host-group", "simple", "TOOLCHAIN_DIGEST", "trusted-development", 4, true

startup_resources |kind, preload, access|
    "compiler-tables", "required", "immutable"
    "stdlib-summary", "bounded-prefetch", "immutable"
    "source-index", "lazy", "group-mutable"
    "single-flight-directory", "required", "group-mutable"

fallback |reason, mode|
    "provider-unqualified", "isolated-process"
    "group-crash", "fresh-isolated-process"
    "untrusted-action", "sandbox-process"
```

Mutable startup indexes stay inside the group by default. Their entries refer to immutable verified payloads, while action-owned scratch stays private. Cross-group mutation requires a separate fixed-layout, versioned, process-shared ABI and explicit owner-death behavior; it is not implied by `group-mutable`.

A group's readiness response identifies initialized provider capabilities and the exact toolchain. It must not claim all possible source inputs are preloaded. Ready groups can warm more resources lazily within cache/memory budgets. Policy can drain a group on toolchain replacement, persistent memory growth, repeated failures, or a revoked qualification.

## 6. Resource lifetime and mapping contract

A mapped resource response contains a stable resource ID/digest, binary format/schema, byte length, access class, generation, and scoped lifetime handle. A local OS mapping capability is transferred through the actual IPC capability channel, not reconstructed from its numeric value in another process.

A proposed binary header includes magic, major/minor version, header/payload lengths, endian/layout flags, provider-format identifier, generation, and checksum/digest binding. Validate every offset, span, alignment, index, and integer multiplication before dereference. Offset width is part of the format. An arena larger than 4 GiB cannot silently use 32-bit offsets; chunk it or use a qualified wider format.

Do not place raw pointers, vtables, STL containers, OS mutex internals, or object addresses in a portable payload. Internal process-local handles are legal only behind the in-process adapter and may not escape its lifetime. Shared synchronization layouts can be host-specific but must negotiate exact ABI and cannot be treated as portable persisted data.

Read-only mappings protect consumers only to the extent that writable aliases/backing objects are controlled. A final artifact must not remain writable through another untrusted mapping or hardlink. Shared source payloads originate from immutable snapshots, not a pathname that an editor can replace during compilation. Resource invalidation means create a new key/generation and retire old references, not mutate bytes under an old digest.

## 7. Provider capability contract

A provider reports resource formats, exact serialization version, supported execution/target profiles, scanning completeness, cancellation support, and qualified isolation modes. Capability names are claims to be admitted against a qualification record, not self-authorizing assertions.

`qualified_group_thread` requires no unsafe process-global mutation, private action-owned compiler state, per-action filesystem/output/diagnostic routing, bounded reset, and grouped-vs-isolated differential tests. `singleplex_process` permits one active action per warm process. `sandbox_process` supplies the required host isolation for untrusted or non-hermetic tools.

The compiler action context receives an explicit snapshot filesystem and output sink. It cannot change process CWD or environment per request, swap stdout/stderr descriptors underneath other compilations, or invoke a global compiler shutdown after one action. Shared log streams are group diagnostics only; user-visible diagnostics are tagged and stored per action.

Simple and Clang both implement this contract but expose different resource formats. A Clang PCH/PCM/BMI is not a Simple `.tld`; the service shares storage/lifetime/identity semantics, not a universal AST representation. Clang's serialization boundary and LLVM's private-context concurrency model guide that adapter. [W02] [W05]

## 8. Native/cross execution and scheduling messages

A compile request identifies both execution and output target requirements. A test request additionally identifies where and how the artifact must run: native host, emulator, VM, SimpleOS image, GPU/driver profile, or a specific class of physical board. The scheduler returns an explicit unavailable-capability reason when no matching worker exists.

Resource claims distinguish divisible capacity from exclusive devices. CPU and memory are capacity claims; a board, JTAG probe, licensed seat, physical GPU reset domain, or dedicated network fixture can be a lease. Device lease loss follows reconciliation/reset rules, not ordinary compile resubmission.

Cancellation has a request ID and current attempt fence. It first detaches one consumer of shared work, then cancels the underlying action only when policy permits. If cancellation cannot stop an isolated action cleanly, its process tree is terminated; if a grouped thread cannot stop, the group is retired. Expired attempts cannot publish.

## 9. Receipt structure and trust

A receipt reports work that actually happened or exact qualified cache evidence that was reused. Include expected action/test IDs and observed outcomes, not only counts. Counts help detect empty runs but cannot detect every substituted test. Store complete case identifiers for manageable suites and authenticated manifests for large sharded suites.

Bind receipts to policy and issuer scope. A local developer receipt can accelerate local workflow but is not automatically a release attestation. A PR cannot authorize its own weaker gate by changing its SDN policy. Validate under the protected baseline policy, with separately reviewed policy migrations. GitHub receives the resulting status from the trusted admission adapter; arbitrary process output cannot directly set that status.

## 10. Protocol and artifact tests

Test SDN/binary typed round trips, field-order invariance, ordered-argument differences, malformed text, duplicate/unknown mandatory fields, length/overflow bounds, decompression limits, byte-versus-text handling, incompatible provider layouts, wrong digest/length, stale capabilities, and unauthorized tenant/resource access.

Provide inspect/explain commands that render binary ring/resource metadata as SDN without changing its semantic identity. Capture a replayable SDN request plus pinned resource digests for debugging, excluding secrets. The transport must permit protocol evolution independently from a particular compiler's AST format.

## References

[R05]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/src/compiler/80.driver/cache/action_key.spl "Simple canonical action key and textual interface extraction; inspected lines 1–230"
[R10]: https://github.com/ormastes/simple/blob/ed75897fe050d874ce7c7bcd90c2b30953ad65ce/config/check/must_check_gates.sdn "Simple canonical must-check registry; opening portion inspected"
[W02]: https://clang.llvm.org/docs/PCHInternals.html "Clang: precompiled headers and modules internals"
[W05]: https://llvm.org/docs/ProgrammersManual.html#threads-and-llvm "LLVM Programmer’s Manual: threads and LLVMContext"
