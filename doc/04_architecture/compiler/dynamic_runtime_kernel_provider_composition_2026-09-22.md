<!-- codex-architecture -->

# Dynamic runtime, aspect, and kernel/provider composition

Date: 2026-09-22. Status: integration design; implementation and native evidence
remain separate gates. This is an additive reconciliation of the selected
runtime-provider, kernel-migration, and environment-variant plans. It does not
replace their requirements or select outstanding aspect language options.

## Authority and scope

The user requested parallel macOS fixes, bootstrap, dynload/aspect review, and
as much practical dynamic-library composition as planned. Existing selections:

- [Runtime optional providers](../../02_requirements/feature/runtime_optional_provider_binary_size_optimization.md): metadata-only registration, exact closure, admitted demand loading, pure-Simple preference after qualification.
- [Kernel migration](../../02_requirements/feature/kernel_plugin_migration.md): K0/K1/P classification, ABI epoch 1, canonical `simple.sdn`, selected LLVM/Cranelift K1 composition.
- [Environment variants](../../02_requirements/feature/environment_optimized_dynamic_libraries.md): selected bounded catalog and typed provider pilot.
- [Aspect options](../../02_requirements/feature/aspect_dynload_options.md): still marked awaiting selection. This document does not authorize transparent acquisition, signing/compression profiles, or hot replacement beyond an admitted contract.

Knowledge routing consumes
`.spipe/environment_optimized_dynamic_libraries/knowledge_selection.sdn` for
compiler/runtime/library owners. Its coverage excludes `src/os`; it is not a
valid kernel/driver receipt. Any later OS implementation must refresh that
route with `mdsoc_only` for `src/os/kernel/**` and `src/os/drivers/**`.

## Observed source and immediate gates

| Boundary | Current evidence | Required qualification |
|---|---|---|
| Composition query | `src/lib/nogc_sync_mut/composition/provider_contract.spl` defines fixed records and `SimpleAbiDigest256V1` | Legacy `u64` digest fields are not full artifact authentication |
| Native provider adapter | `src/os/smf/kernel_plugin/native_loader.spl` wraps provider sessions and generation pins | Native mapped payload must execute through the admitted interface |
| Runtime dynload | `src/runtime/runtime_dynload.c` owns native mapping primitives and provider machinery | Optional platform implementation must not become a base executable root |
| Darwin manifest | `src/compiler/00.common/cache/darwin_runtime_provider_manifest.spl` validates Mach-O/archive identity | Bind exact target, complete dynamic dependencies, symbol ownership, and bytes actually mapped |
| Aspect leases | `src/lib/common/aspect_dynload_lifecycle_v1.spl` explicitly requires external lifecycle serialization | Counters alone prove neither concurrency safety nor physical unmap |
| Bootstrap authority | `scripts/bootstrap/phase2-runtime-capsule.shs` snapshots compiler/native archive/hosted rlib without the runtime cdylib; authority owner confirms matching gap in bootstrap tuple | P0: freeze/hash the actual cdylib before dynamic runtime qualification; archive identity is insufficient |
| Cocoa | Current lane decision: `rt_cocoa_*` has one implementation owner in the runtime dynload provider | No second statically retained implementation; exact dynamic artifact/symbol evidence |

The historical assertion that a runtime shared library cannot exist in
`plugin_arch/kernel_pluggable_partition.md` is an old observation, not a
restriction on provider packaging. Its K0 trust-root rule still applies.

## Partition and placement

Closure membership and binary placement are independent. A dynamic artifact is
useful only when its dependency closure and lifecycle are smaller and stable.
Do not split every function into a DSO or force per-node indirect calls.

| Keep in admitted core/composition | Extract or retain as optional provider | Why |
|---|---|---|
| Minimal value/allocator ABI, loader trampoline, admission roots, error path | Cocoa UI, GPU vendors, audio/media, database/compression/crypto implementations when optional | Loading must not depend on the provider it is trying to validate |
| Compiler K0 grammar, HIR/MIR ownership, weaver, identity computation | Advice bodies, tooling packs, coarse lint/provider sessions, qualified runtime services | Stable coarse seams avoid exposing compiler-private layouts |
| Selected K1 LLVM/Cranelift bootstrap composition, MIR-internal optimizers | Non-bootstrap backends after stable seam qualification | Preserve existing selected bootstrap and internal MIR contracts |
| SimpleOS early boot, interrupts, scheduler/MMU and required device bootstrap | Admitted userland services; later kernel modules only under kernel capabilities and resident bounds | Hosted `.dylib`/`.so` is not an early-boot kernel module |

`dynload` stays the ordinary pure-Simple composition mode; `one-binary` stays
the explicit closed deployment mode. Static placement uses the same interface,
capability and artifact identity contract. Missing or rejected dynamic providers
return typed unavailable errors. They do not silently select an unrecorded
archive, source interpreter, Rust seed, or second implementation. A declared
`prefer` policy may select a pre-admitted alternative before effect execution;
`require` fails. An effectful operation is never replayed in a fallback provider.

## MDSOC and existing authorities

`common` owns `IfaceId`, `ParamHeader`, `ParamExt`, fixed wire records and reason
codes. Composition owns SCI decoding, admission, dense tables and generation
publication. Loader adapters own mapping and platform callability. Domain
providers own semantics; consumers cannot access sibling-private state.

Reuse `SimpleCompositionImageV1`, `SimpleProviderQueryV1`, KPF generations and
`ProviderLoaderSessionV1`; do not create another catalog authority or lifecycle.
An adapter may project an existing version into a newer record but must retain
the source identity. Stable ABI records carry fixed widths, bounded offsets,
opaque handles, explicit buffer ownership and calling convention. They do not
carry Simple collections, closures, AST/HIR/MIR objects or allocator-private
pointers. Version evolution is append-only within an admitted minor contract;
new required fields and incompatible major/schema are rejected.

Compile-time feature transforms/weaving remain compiler authority. A runtime
provider adapter selects an implementation. An aspect pack publishes guarded
advice/facet bindings. These are different operations: loading a native library
does not establish that an aspect was activated or that its payload executed.
The exact binding-plan, pack, mapping-receipt and generation identities must
join before a dynamic-aspect execution claim. Existing static `.try_facet<F>()`
behavior is preserved while acquisition requirements remain unselected.

## Manifest and load transaction

`simple.sdn` is the canonical authored plugin manifest; generated SCI/lock and
bootstrap receipts are derived authority projections, not parallel manifests.
Bind provider/interface IDs, ABI epoch and full ABI digest, target/architecture,
artifact format and content digest, dependency-lock digest, exported operation
table, effect/capability policy, bounded resources, and tool/source provenance.
Digest equality identifies bytes; publisher authentication requires separately
admitted trust policy. No truncated digest or filename/version match is enough.

The transaction is: inert bounded decode; dependency/policy/target admission;
freeze exact artifact and dependency identities; map; query compatible ABI;
prepare bounded state; run admitted self-check; atomically publish generation.
Native constructors can run at mapping, so artifact and dependency admission
precedes mapping. Post-map query cannot retroactively authenticate executed
constructors. If the platform cannot establish that inspected bytes are the
mapped bytes, admission fails; a mutable-path pre-hash/post-hash pair alone
does not close the race. Untrusted native code needs an existing worker boundary.

Cocoa exports resolve from the exact admitted runtime provider handle, not an
ambient process-symbol search. Legacy name discovery is a migration adapter,
not permission to load arbitrary search-path candidates. Cocoa lifecycle and
thread affinity remain its domain owner's responsibility. Optional AppKit/GPU
initialization occurs only on actual capability demand.

### Cocoa artifact ownership and toolchain boundary

`src/compiler_rust/runtime/Cargo.toml` emits `rlib`, `staticlib` and `cdylib`
from one crate. A feature check excluding `native-all-provider` alone cannot
prove Cocoa exists only in the cdylib: the standalone crate's static outputs
share that feature graph. The current integration accepts the Cocoa owner's
cdylib-only linker-argument placement plus `DynamicSymbolProvider` resolution
as a transitional mechanism, conditional on symbol inspection of all three
outputs and exact admitted-handle selection. Implementation bodies in
`src/runtime/hosted_cocoa.c` must not enter static/rlib/native-all archives.

Keep this small artifact-scoped mechanism while it satisfies the ABI/export
and toolchain gates. A separate provider cdylib target/crate is the preferred
long-term boundary if artifact-scoped linking becomes fragile or additional
platform providers need independent release/identity. That later packaging
change must preserve the selected runtime provider contract and migration path;
it is not an extra requirement for the current bootstrap repair.

The macOS lane also reports LLVM 23 `ld64.lld` failure on generated
`objc_msgSendClass$` stubs. Record exact Objective-C compiler, linker and flags
in producer identity and prove the chosen supported lowering/linker combination
on an actual Cocoa operation. A successful archive build is insufficient; do
not publish a dylib whose callable exports or Objective-C dispatch fail.

## Generations, cache and invalidation

Single-flight loading is keyed by provider, artifact/dependency digest, target,
ABI, catalog/policy/environment generation and composition identity. Cache
rejections only for that key. Replacement changes generation; filename, size
and mtime alone are not cache identities. Bounded metadata indices are prepared
once; requests use pinned dense operation slots.

Publication preserves the prior generation on failure. Retire only after calls,
callbacks, aspect continuations, relocated references, sessions, buffers and
device fences quiesce under the canonical owner. Cancellation and successful
`dlclose` are not proof of physical unmap. Retain mappings when the platform or
provider lacks proved unload support; report that state honestly.

A provider-body edit rebuilds that provider and derived artifact/lock receipts;
it need not recompile unaffected K0 objects. ABI edits invalidate consumers of
that interface. K0/loader/value-ABI edits invalidate affected kernel authority.
Static aspect edits invalidate woven call sites through dependency manifests;
dynamic aspect changes use guarded registry generations and leases. Incomplete
dependency knowledge triggers a recorded conservative invalidation.

## Performance and rollout gates

Use the selected budgets without inventing broader aspect thresholds:
KPM startup metadata/negotiation adds **less than 2 ms** to the measured CLI
baseline; no optional-provider hello loads/initializes any optional DSO.
Environment-variant selection p95 is **1 ms warm / 25 ms cold**, dense batch
dispatch overhead **at most 2%**, inactive catalog RSS **at most 2 MiB**, and
selected-provider RSS increase **at most 5%** on its named fixture. These are
scoped gates, not claims that first-use library mapping takes 1 ms. Preserve
runtime-provider size and interpreter baseline requirements as separate gates.

Report selection, verify, map, initialize, publish, first call and warm call
timings separately, with full artifact identity, mapped text, RSS and rejection
counters. No filesystem scan, environment parse, hashing, symbol lookup or
process spawn belongs on the warm operation path. Keep MCP/LSP startup core
closure small; command-family loading happens at a coarse admitted boundary.

Migration order: P0 authority/cdylib integrity; sole-owner Cocoa runtime load;
coarse optional providers; static/dynamic parity and invalidation; true mapped
aspect payload integration after selected requirements; only then broader
provider promotion and supported-platform qualification. Each phase requires
positive execution plus a mutation that fails the same gate. Bootstrap uses
admitted immutable input generations and preserves prior usable generations.

## Handoff

- [Detail design](../../05_design/compiler/dynamic_runtime_kernel_provider_composition_2026-09-22.md)
- [Test plan](../../03_plan/sys_test/dynamic_runtime_kernel_provider_composition_2026-09-22.md)
- [Agent ownership](../../03_plan/agent_tasks/dynamic_runtime_kernel_provider_composition_2026-09-22.md)
- [Existing KPF architecture](../kernel_plugin/kernel_plugin_fabric_architecture.md)
- [Environment variant architecture](environment_optimized_dynamic_libraries.md)
- [TLDR](dynamic_runtime_kernel_provider_composition_2026-09-22_tldr.md)
