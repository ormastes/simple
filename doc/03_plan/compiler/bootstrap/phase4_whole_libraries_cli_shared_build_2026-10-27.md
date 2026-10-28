# Phase 4 whole-library and CLI build plan

Date: 2026-10-27. Status: **PLAN; implementation and native verification pending**.
Requested scope: divide the build into library and CLI product tasks, include the
whole library/tool inventory in Phase 4, and build each shared library once for
reuse by all compatible executable consumers.

## Source and execution authority

This plan initially binds release commit
`65055a380bb92366e375ee499be86d8daad388fb`, fetched directly from
`origin release/1.0.0`; `FETCH_HEAD`, rather than a possibly stale tracking ref,
was inspected. The worktree is `/tmp/simple-phase4-whole-products-plan-20261027`,
branch `work/phase4-whole-products-plan-20261027`. The original checkout,
unrelated documents, running aarch64 buildrunner build, and existing caches were
not changed. No compiler, bootstrap, product build, test suite, or deployment was
started for this planning task.

At implementation start, fetch the selected release again, record its actual SHA,
and make one bounded comparison with exact main and existing relevant work. The
source closure, reviewed applicable fixes, manager image provenance, runtime,
host policy and tools become immutable before execution. Do not update a live
build's source, producer, helper scripts, configuration, or caches. Integration
of later fixes takes place only at the next authorized restart; retain original
failure evidence and compatibility-qualified cache objects. This plan does not
select unrelated fixes or authorize release publication.

## Existing implementation and gaps

| Surface | Observed implementation | Required integration |
|---|---|---|
| `scripts/bootstrap/lib/managed-task-schedule.shs` | Six Phase 4 executable entries per LLVM/Cranelift backend; one Phase 3 bootstrap entry per backend; module/index and subsystem rows | Generate product tasks from a complete classified inventory instead of treating six entries as the whole product set |
| `scripts/bootstrap/bootstrap-phase4-grouped.shs` | Pinned source/runtime/manager authorities, private per-product caches, broad source roots, typed index handoffs and compiled task owner | Preserve these authorities; introduce explicit library producers and immutable library consumer inputs |
| `scripts/bootstrap/prepare-phase4-native-groups.shs` | Inventory-driven native module/SMF collection | Preserve module coverage separately from public library artifacts and executable coverage |
| `src/app/bootstrap_builder/managed_producer_factory.spl`, `managed_product_wave.spl` and `managed_inventory_join.spl` | Existing producer-wave/inventory extension points | Bind actual newly produced compilers and library manifests between waves; do not predeclare imaginary hashes |
| `src/app/buildrunner/runner.spl` | Adapter to `std.common.task_runner.scheduler` | Reuse the parent-owned scheduler and ledger; no second shell scheduler or independent resource owner |
| `src/app/build/scheduler/parent_graph_*` and `parent_issued_graph_*` | Parent-issued graph and wave preparation | Add typed library dependency/output contracts and preserve deterministic parent commit |
| `src/compiler/80.driver/driver_aot_native_output.spl` | Native `--emit-archive` and `--emit-shared` paths already exist | Qualify these paths with actual package closures, PIC, symbols, initialization, runtime and consumer linking |
| `src/compiler/80.driver/driver_build/native_link_receipt_v1.spl` | Shared-link receipts bind object and tool/runtime digests | Extend/consume the identity contract; an existing link cache alone does not prove cross-binary library reuse |
| `src/app/build/scheduler/parent_artifact_export.spl` | Executable ELF validation rejects `DT_SONAME` | Add a separate shared-library artifact profile; retain executable-profile rejection |
| `scripts/setup/install-runtime-shared-library.shs` | Versioned native runtime installation; acknowledges static/bootstrap and loader-less targets | Keep runtime artifacts distinct from Simple packages and SMF modules |

The six currently scheduled Phase 4 entries are bootstrap
(`src/app/cli/bootstrap_main.spl`), full CLI
(`src/app/cli/_CliMain/main_and_help.spl`), interpreter
(`src/app/cli/interpreter_main.spl`), MCP (`src/app/mcp/main.spl`), LSP
(`src/app/simple_lsp_mcp/main.spl`) and runner
(`src/app/test_runner_new/main.spl`). Existing entrypoint aliases must be resolved
against the frozen release; an entry named `main.spl` is not automatically a
standalone shipping product. The review must explicitly include buildrunner,
bootstrap/build managers, standalone command tools and all CLI-dispatched tools.

Existing shared parse CAS, HIR/object caching, an SMF file, and a shared native
library are different artifacts. None substitutes for the requested property:
two different binary consumers link and execute using the same admitted shared
library bytes without independently compiling its owned implementation again.

The existing runtime design, `doc/05_design/runtime/dynamic_library/shared_runtime_libraries.md`,
documents that Stage 4 links static `libsimple_native_all.a`, while
`libsimple_runtime`'s shared export surface is incomplete for substitution. Its
568-symbol gap (including 350 C exports) is a documented measurement, not a new
measurement made here. Recheck the exact selected runtime before implementation;
do not quietly switch consumers to that cdylib or mistake runtime reuse for
Simple-package library reuse. Existing static bootstrap lanes remain separate
from the requested hosted shared-library qualification.

## Inventory is the completeness authority

Create a versioned canonical SDN product inventory and generated closure digest.
Use tracked package/module manifests, package ownership, composition variants,
CLI dispatch/help declarations, supported wrappers and product entry declarations
as primary inputs. Reconcile them with tracked source paths once per snapshot.
Do not maintain a handpicked binary list or discover the whole tree repeatedly in
each build worker.

Verified seed authorities on the pinned release are:

| Manifest | Declared package/type | Ownership namespace |
|---|---|---|
| `src/lib/simple.sdn` | `simple-std`, library | `simple.std` |
| `src/compiler/simple.sdn` | `simple-compiler`, application | `simple.compiler` |
| `src/compiler/00.common/simple.sdn` | `simple-compiler-common`, library | `simple.compiler.common` |
| `src/runtime/simple.sdn` | `simple.runtime`, library | `simple.runtime` |
| `src/app/simple.sdn` | `simple-app`, application | `simple.app` |

`src/package_ownership/simple.sdn` also declares compositions, generated,
hardware, i18n, OS, plugins (and nested backend_wasm), compiler_rust, test_fixture,
tool, tooling, type, unit, verification and `examples/10_tooling` ownership roots.
Some roots intentionally have no package manifest. Reconcile them explicitly;
neither an ownership namespace nor an application package declaration proves a
standalone shared-library target. Compiler internal libraries require declared
product partitions rather than relabeling the compiler application's manifest.

Inventory all owned library packages under `src/lib`, compiler libraries and
`src/compiler/90.tools`, app libraries/tools under `src/app`, plugin products,
`src/package_ownership`, composition selectors and supported `src/os` products.
Register runtime C/native components separately; treat vendored sources as
external dependency inputs, not owned library coverage. Include tool subcommands
implemented inside the full CLI without manufacturing one binary per subcommand.
Use the repository's actual package ownership and namespace rules: a directory
or `.spl` file is not automatically a linkable library.

Each product row declares: stable product ID; kind (`shared_library`,
`static_archive`, `smf_module`, `header_or_source_package`, `executable`,
`cli_subcommand`, `test_product`, or `external_runtime`); package/export roots;
entry when applicable; public interface; dependency IDs; source closure;
platform/backend predicates; resource class; generated inputs; runtime/loader
requirements; build and behavioral verification tasks; and disposition.

Every discovered candidate must resolve to a product, a covered internal module,
an alias of another product, a test/example, or an explicit exclusion with reason,
owner and platform/profile condition. Unsupported requested targets remain
`BLOCKED`/`UNSUPPORTED`; exclusions must never turn an incomplete full profile into
PASS. Entire library coverage includes generic/source-only libraries through
typecheck/import and concrete consumer instantiation tests even where emitting a
standalone shared object is inapplicable. Product counts are generated facts,
not a hardcoded acceptance target. Missing, duplicate, cyclic, conflicting or
unclassified ownership rows reject inventory admission.

## Phase and dependency graph

1. **Prepare** freezes source and classification inventory, selected platform,
   producer authorities, host/backend tools, runtime and resource policy. Compile
   and admit changed manager images from the same source authority before using
   changed shell transports. Existing admitted producer caches may be read only
   through matching immutable identity.
2. **Phase 1** prepares the seed and collects its whole test inventory to terminal
   summary. A usable exact producer still requires compile-and-run sanity;
   retained failures do not become qualification.
3. **Phase 2** builds and sanity-checks each requested compiler. Then build,
   enumerate and execute compiler/interpreter/loader subsystem test products for
   each backend. Following exact Hello compile/link/run sanity, schedule Phase 3
   and the early `phase4/from-phase2/<producer-digest>` product cohort alongside
   independent Phase 2 tests. Descendants remain provisional until admission.
4. **Phase 3** builds and sanity-checks the new compiler. Its complete tools and
   library test inventory overlaps the final
   `phase4/from-phase3/<producer-digest>` cohort. Preserve campaign-specific
   Phase 3 priority and any previously imposed serialized-compiler policy.
5. **Phase 4A — libraries:** resolve package graph and build each eligible shared
   library, runtime variant, static archive or SMF product at its own dependency
   boundary. Independent components run within admitted resources. Publish
   immutable artifact/interface manifests only after cleanup and validation.
6. **Phase 4B — tools:** as each executable's own dependencies become ready,
   compile its entry and consumer-owned modules, then link against the exact
   library manifests. No global all-libraries barrier and no per-tool rebuild
   of previously built library-owned modules. Generic specialization ownership
   is explicit; tool-specific specializations remain consumer-owned.
7. **Phase 4C — evidence:** execute library ABI/load behavior, each tool's real
   smoke scenario, MCP/LSP protocol checks and the entire classified test
   inventory through the cohort's exact full CLI/runner. Retain early and final
   cohort evidence independently. A Phase 4-produced full CLI/runner and its
   command-owner receipt are additionally required for existing Phase 4
   self-host qualification; a Phase 3-built runner cannot stand in for it.
8. **Finalize:** parent joins immutable manifests, terminal statuses and test
   counts. Required blocked/failed/not-run rows prevent qualification. Stage 4
   evidence does not replace later repository-wide release qualification.

Library and binary work therefore interleaves by dependency. Discovering a new
producer/library output creates a validated child wave with actual digests,
bounded task count, inherited deadline and resource authority. Reject cycles,
duplicate node identities, references outside the admitted closure and attempts
to replace completed inputs. Dynamic import/reflection/plugin/AOP/weaving
dependencies must be represented by explicit registries or conservative closure
inputs; a hidden dependency invalidates the affected plan. Do not mutate a running
node's sealed inputs or infer closure solely from plain `use` statements.

## Build once and reuse: compatibility and ABI contract

“Once” means once successfully published per exact compatible library key, not
once globally across architectures, changed source, different producers or both
backend cohorts. A failed attempt may resume validated object checkpoints under
the same identity and bounded retry policy. All compatible consumers reference
the same published artifact digest.

The library key binds schema version, package/owned source and generated-source
digests, ordered source roots/overlays, source closure and resolved dependencies,
actual compiler byte digest and admitted provenance, codegen backend/version,
host and target triples, CPU features, object format, codegen/optimization/debug/
sanitizer/PIC flags, native tools, runtime/GC/allocator/thread ABI, public symbols
and calling conventions, data layout and generic/monomorphization policy, module
initialization ABI, exception/unwind behavior, loader/SMF/AOP ABI where used,
feature/configuration policy and dependency interface/artifact digests. Unknown
compatibility rebuilds conservatively; matching names or mtimes are insufficient.

Keep full source authority for provenance while using a validated package closure
fingerprint for narrow reuse. Unrelated repository changes can preserve a library
artifact only when closure discovery is qualified and excluded global policies
cannot affect it. Otherwise use the full snapshot digest and accept conservative
rebuilds. LLVM and Cranelift and Phase 2/3 producer hashes have separate keys by
default; no cross-producer reuse based only on an asserted ABI version.

Before partitioning packages, define export ownership, symbol visibility,
initialization order and single ownership of global state, allocators and runtime
registries. Reject accidental duplicate definitions/initializers, mixed GC/runtime
instances and memory freed by a different ABI owner. Generic bodies may need to
remain in interface/source packages; verify representative concrete instantiations
and do not claim their consumer-specific code is a shared artifact. Cyclic library
clusters require reviewed coalescing into one library or a documented link-group
strategy; the scheduler must not pretend a cyclic graph is a DAG.

Each published manifest contains exact artifact bytes, interface/export digest,
runtime/dependency closure, producer/source identities, link mode, import library
when needed, required loader identity, validation receipts and evidence state.
Consumers seal those manifests before compilation/linking. Their link receipts
bind library artifact digests as well as interfaces: even ABI-compatible changed
bytes require renewed package/runtime evidence. Record true consumer reuse
separately from link-cache hits and object-cache hits.

## Cache, process and commit ownership

Use a stable lineage root containing `libraries/<library-key>/`,
`products/<product-id>/<consumer-key>/`, and `evidence/<cohort>/`. Concrete storage
placement follows the existing centralized-storage policy. A library node alone
owns its writable frontend/HIR/native staging, object cache and link outputs.
Executable nodes have private writable caches. Never point concurrent binary
workers at one writable native cache to achieve “reuse.”

Validated immutable parse/object CAS entries can be shared with explicit read
authority; publication uses create-once/atomic content-addressed commit. One
parent grants a lease per library key, deduplicates ready requests, verifies base
revision and child result, and commits in deterministic graph order. Children
consume frozen inputs and return owned results. The parent rejects stale results,
changed manifests and out-of-scope writes. Temporary results are inaccessible to
consumers until validation and successful process-tree cleanup.

Reserve frontend RSS, codegen threads, memory, disk and wall time separately.
Existing lane-specific serialization overrides broad parallelism. Waiters do not
create second writers. Cancellation/timeout kills only the owned process tree,
drains bounded result transport, records cleanup outcome and retains diagnostic
outputs. Unconfirmed cleanup retains the lease/resources and blocks reuse.
Cancellation of one consumer cannot delete a shared artifact or cancel a library
still needed by another consumer; only the parent decides when no dependents
remain. Crash-resume checks owner liveness, artifact hashes and journal commit
before reusing a checkpoint. No PID-name kills, live-cache removal, restamped
receipts or retry loops on unchanged failures.

## Backend and platform boundaries

| Profile | Required library and consumer proof |
|---|---|
| Linux/FreeBSD ELF | Correct target/PIC, exported symbols, SONAME, dependency and loader paths; two distinct linked consumers actually run with the pinned `.so` |
| Windows PE/COFF | DLL and import-library identity, exports, calling convention, CRT/allocator compatibility and controlled DLL search path; run both consumers on Windows |
| macOS Mach-O | Dylib install name, compatibility version, rpaths, architecture and runtime compatibility; run on macOS; preserve the existing Cranelift `llvm-ar` restriction for archives |
| LLVM/Cranelift | Independent backend/toolchain identities and actual emitted/link/run evidence; one backend's PASS does not cover the other |
| Cross/native host differences | Cross-link is build evidence only; runtime assertions require the selected native host or recorded VM/emulator |
| SimpleOS/freestanding/no loader | Explicit static/archive profile with compatible compile-once object/archive reuse; never label this as shared-library runtime qualification |
| CUDA/GPU/optional plugins | Pin selected host/device policy and dependencies; unsupported/disabled products are explicit scope dispositions, not fabricated successful tests |

Do not impose dynamic linking universally. The full profile must represent every
selected target and honestly distinguish shared, static, SMF and source-only
coverage. Prefer relocatable packaged loader paths and stage tests outside the
build directory so ambient libraries cannot make missing dependencies pass.

## Implementation lanes and shared interfaces

The implementation owner first freezes these proposed interfaces:
`Phase4ProductInventoryV1`, `Phase4ProductV1`, `Phase4LibraryIdentityV1`,
`Phase4LibraryArtifactV1`, and `Phase4ConsumerInputsV1`. They are design names,
not claims that those types already exist. Extend existing graph/task contracts
through versioned adapters rather than incompatible positional changes.

| Lane | Owned scope | Handoff and dependency |
|---|---|---|
| A — inventory | Product classification/generator, SDN schema, closure reconciliation | Frozen inventory and exclusions; architecture owner reviews completeness before scheduling |
| B — library products | Compiler emission, interfaces/export ownership, native library manifests, typed artifact profiles | Uses A's identities; proves one library and two real consumers before widening inventory |
| C — scheduler/cache | Existing parent graph/task owner, leases, dynamic producer binding and resource/cancel behavior | Consumes frozen A/B contracts; no competing shell executor |
| D — CLI integration | Managed phase scripts as argument transport, full-cli/runner and all tool entries | Uses B/C manifests; update canonical and provisional paths together without admitting provisional work |
| E — evidence | SPipe scenarios, test inventory, platform/backend matrix and manual generation | Real assertions and actual counts; generated manual review by high-capability reviewer |
| Merge owner | Integrates in A → B/C → D/E order, checks overlapping edits, freezes final candidate | Exact-head review, focused checks, then authorized PR landing; no release tag/publication |
| Final reviewer | High-capability review of inventory, exclusions, ABI/ownership and executed evidence | Distinguishes source-reviewed, fixture-tested, native-tested and formally admitted claims |

Lower-model sidecars may collect inventories or implement bounded contract-stable
work. They cannot accept completeness, exclusions or qualification. This planning
run uses one read-only inventory sidecar; no implementation work is delegated.

## Acceptance and bounded verification

Create executable SPipe scenarios under
`test/03_system/app/bootstrap_builder/feature/`; generated/manual documentation
belongs only in matching `doc/06_spec/.../*.md`. Proposed common steps are
`freeze_phase4_inventory`, `build_shared_library_once`,
`build_two_library_consumers`, `run_library_consumers`,
`verify_library_reuse_receipts`, and `cancel_owned_build_tree`. Missing harness
behavior fails explicitly; never create placeholder passes.

| ID | Real acceptance evidence |
|---|---|
| P4-001 | Frozen inventory reconciles every owned package/tool candidate, resolves CLI aliases and has no missing/duplicate/unclassified required rows; deliberate orphan/duplicate fixtures are rejected |
| P4-002 | A nontrivial shared library exports stateful and data-passing behavior; two distinct real binary consumers link and run against exactly one artifact digest; compilation/event receipts show one library publication and no library-owned recompilation inside either consumer |
| P4-003 | Warm repeat of the same task graph uses validated library/artifact receipts with zero library recompiles; binary-local edit rebuilds that consumer only; library implementation/interface, runtime, producer, target, backend and feature mutations invalidate the appropriate nodes |
| P4-004 | Shared-state initialization, allocator ownership, generic specialization, exports and missing-symbol errors behave correctly; malformed ABI/manifest and duplicate ownership are rejected before successful consumer admission |
| P4-005 | Concurrent consumers request one library key; exactly one lease/writer wins, partial library bytes remain invisible, randomized completion yields the same committed graph result |
| P4-006 | Cancel one consumer while another waits/executes; needed library remains valid. Inject child crash, timeout and stale lease; owned descendants are reaped or resources remain held, no consumer accepts incomplete output |
| P4-007 | Fresh compiler-produced next waves bind actual producer hashes after real Hello execution; unknown dependency/cycle/stale snapshot is rejected. Phase2 and Phase3 cohorts never overwrite/substitute each other's evidence |
| P4-008 | Every selected standalone tool runs its behavioral smoke; full CLI dispatches real check/test operations; test rows report discovered/executed/pass/fail/blocked counts with positive assertions and no skipped-only success |
| P4-009 | MCP and LSP execute pinned initialize/initialized/tools-list plus status/symbol operations; child command-owner identity is checked before and after, with no ambient deployed binary substitution |
| P4-010 | ELF/PE/Mach-O supported profiles retain their real native link/load/run evidence, and shared artifacts pass a shared-library validator while executable validators still reject them; static/no-loader profiles remain explicitly separate |
| P4-011 | Whole library/module and tools inventory reaches a terminal summary despite independent deterministic failures; required failures, omissions, timeouts and blocked rows prevent qualification |
| P4-012 | Representative cold/warm graph timings, library/frontend compile counts, consumer link time and peak RSS are recorded; warm reuse demonstrably removes duplicate library work without broad repeated source scans |

Run each unchanged passing acceptance check once. Reserve integration checks for
the implementation (compiler/lib/MCP/LSP checks, MCP stdio integration, core
runtime/native server smokes, direct-env guards, and spec-layout audit). Shell
transport fixtures do not qualify native manager enforcement, ABI correctness or
runtime load behavior. Cap repair/verify cycles at six overall, retain original
failures and stop earlier on unchanged failures; apply any stricter three-cycle
per-cause campaign limit. Do not launch new full bootstraps merely to review this
document. No native PASS, coverage percentage, performance improvement or release
readiness is claimed by this plan.
