<!-- codex-design -->

# Detail Design: Minimal-Bootstrap Configuration-Composed Dynamic Architecture

## Scope and sequencing

Implementation proceeds as independently reviewable vertical slices: wire-format/target prerequisites; composition compiler/reader; app catalog proof; leaf CLI provider proof; compatibility scheduler; coarse compiler provider; workflow documentation. The first accepted implementation need not claim later slices complete.

## Shared public names

These names are frozen for all lanes; changing one requires architecture review:

- `SimpleCompositionImageV1`
- `SimpleProviderQueryV1`
- `SimpleCliCommandV1`
- `SimpleAppLaunchV1`
- manual flows: `compile_composition`, `load_unchanged_core`, `dispatch_provider`, `explain_rebuild`
- setup/checkers: `setup_minimal_bootstrap_fixture`, `check_composition_image`, `check_rebuild_receipt`, `check_bootstrap_reason`

Incomplete scenario helpers call `assert(false)` or `fail(...)`; they never return a passing constant.

## Proposed module ownership

Exact numbered placement is confirmed against concurrent target-graph work before creation, but responsibilities remain fixed:

| Package | Responsibility |
|---|---|
| `src/spec/composition/` | v1 source schema and generated/shared identities |
| `src/lib/nogc_sync_mut/composition/` | dependency-light wire structs, canonical codec, validation, indexed read-only view |
| `src/app/configc/` | SDN parse/overlay/normalize/validate/lock/write/read-back command |
| `src/app/build/` | named targets, typed edges, compatibility decision, action/CAS receipt, explain output |
| `src/app/startup/` | core composition adapter and provider activation orchestration |
| `src/os/smf/` and native loader owners | mapping plus process-callable query bridge |
| `src/os/services/launcher/` | app-record adapter and lifecycle state |
| CLI command registry owner | SCI summary lookup and `SimpleCliCommandV1` dispatch |

Common wire/contracts remain above consumers. Launcher, CLI, and compiler providers cannot import one another's private implementation trees.

## Composition IR and wire records

`CompositionIrV1` contains normalized schema/profile identities and arrays of interface groups, providers, bindings, commands, apps, associations, launch policies, targets/edges, generated-file ownership, and provenance. Source spans remain diagnostic-only and do not enter canonical identity.

`SciHeaderV1` uses fixed-width fields for magic/version/byte order/flags/total size/directory offset/count/schema digest/composition digest. `SciSectionEntryV1` carries section type/version/required flag/offset/length/digest. All offset-plus-length checks use checked arithmetic before access.

Compilation algorithm:

1. parse source and overlays;
2. resolve deterministic precedence and report conflicts;
3. normalize IDs, paths, versions, capabilities, and target labels;
4. validate uniqueness, interface imports/exports, slots, policy, and graph cycles;
5. resolve exact already-built provider identities;
6. canonical-sort records and intern strings;
7. encode and digest each section, then the image;
8. write output atomically;
9. read it back using the runtime reader and compare semantic identity.

The config compiler does not invoke a provider build. A missing artifact is a typed input error naming the required target.

Reader algorithm validates the header and directory completely before decoding any semantic record, then validates cross-record indices and policy before publishing `CompositionViewV1`. The view stores immutable bytes plus indexes; consumers receive bounded views, not copied mutable arrays.

## Provider descriptors

`SimpleProviderRequestV1` fields: struct size, interface ID, minimum major/minor, host ABI digest, target identity, requested capability bitset/view. `SimpleProviderResultV1` fields: status, provided major/minor, descriptor size/address, opaque context, provider identity, implementation digest, ABI digest.

`SimpleCliCommandV1` uses coarse calls for description, argument validation, execution, and completion. SCI duplicates only stable summary/option-schema identity needed for root help. `SimpleAppLaunchV1` accepts an immutable launch request with app/artifact/action IDs and bounded arguments, and returns a stable status plus opaque process/activation identity.

Cross-binary CLI invocation uses canonical arenas, not Simple strings or
collections. The request begins with a fixed 28-byte header followed by the
command UTF-8 bytes and a counted sequence of length-prefixed UTF-8 arguments.
The response begins with a fixed 20-byte header followed by output and
diagnostic UTF-8 bytes. All offsets are arena-relative; decoders require
canonical contiguous ordering, exact terminal bounds, bounded argument counts,
and an explicit output capacity.

Host allocation owns cross-boundary output memory unless a descriptor explicitly states caller storage. Provider exceptions/unwinding cannot cross the boundary. Every operation returns a stable status and writes diagnostics through an explicit sink.

## Provider activation state

`ProviderGeneration` stores provider/artifact identities, mapped library handle, stable queried interface table, capability grant, pin count, and state (`Candidate`, `Active`, `Retiring`, `Closed`). Admission validates path, digest/signature, target/ABI, and process-callable entry. Query results are sampled for required interfaces before atomic activation. A new generation replaces the active index only after full validation; existing handles retain the retiring generation.

## App-catalog slice

The fixture defines one app/provider/binding/association. `simple-configc` produces SCI; the launcher adapter builds ID, alias, shortcut, and association indexes once. The test records the core artifact identity, changes display metadata, recompiles SCI, loads the same core identity, and observes the new record. No source/compiler/bootstrap action may appear in the receipt.

Migration of `launcher_init`, `default_manifests`, and disk aliases must choose SCI as authority. Compatibility importers are temporary, one-way projections and report conflicts instead of precedence-based silent override.

## Leaf CLI slice

Start with a dependency-light existing leaf-tool class (formatter/linter/fixer/TODO scanner after implementation inspection). The root registry resolves its SCI command record, admits its artifact, queries `SimpleCliCommandV1`, validates args, and executes. A private output marker change rebuilds the provider and locked SCI digest only. Core and compiler-provider artifact identities remain unchanged in the receipt.

## Build receipt and compatibility

`BuildExplainReceiptV1` contains requested target; changed files; changed interface groups; old/new implementation, compile-interface, ABI, semantic, tool-behavior, runtime, link, and config-projection digests where relevant; compatibility result; selected closure; reused/rebuilt counts; bootstrap-required flag; typed reason; admitted producer identity.

Each typed edge selects one digest class. An input becomes unknown, its producer is evaluated, then unchanged edge identity marks it green. `Unknown` chooses the smallest producer/stage rebuild. Only `Exact` or proven `Compatible` can reuse. Full bootstrap selection requires a non-empty allowed `BootstrapReason` and a graph path to an explicit bootstrap target.

## Cache and invalidation

Action key inputs are declarative and sorted. Environment inputs use an allowlist. The action cache maps keys to result records; CAS maps content digests to bytes. Namespace includes schema major, producer ABI, target, backend, profile, and artifact kind. No implementation path calls global cache deletion.

SCI has projection identities per section/consumer. App display changes invalidate app/catalog and composition-root identities but not interface schema or command projection identities.

## Diagnostics

Stable categories include malformed image, unsupported required section, overlap/bounds/overflow, digest/signature failure, duplicate binding/interface, undeclared slot, unsafe path, capability denial, artifact missing, unsupported interface major, descriptor too short, unstable provider query, non-callable entry, generation pinned, unknown compatibility, and bootstrap reason required.

Every diagnostic provides category, subject identity, safe context, and remediation. It never dumps raw signed configuration or secrets.

## Performance and evidence

Fixtures include realistic command/app/provider records. Primary acceptance
captures modules parsed/typed/lowered, objects generated, providers packaged,
links performed, SCI sections regenerated, and cache hits/misses. Timing, mapped
bytes, and max RSS are observational with host/producer/sample labels. Full-tree
scans, repeated text reads, and subprocesses remain forbidden. Bootstrap without
a previously emitted typed reason fails before any stage begins.

Detailed implementation follows P0 cheap decisions, P1 core extraction, P2 CLI
configuration, P3 essential provider, P4 leaf providers, P5 per-module cache,
P6 compiler engine provider, P7 full product composition, and P8 release
bootstrap. Each phase consumes the prior phase's structural receipt contract.

## Documentation migration

Update relevant `.codex/skills`, `.agents/skills`, `.claude/skills`, `.claude/agents/spipe`, `.claude/commands`, `.gemini/commands`, `doc/07_guide`, SPipe manuals, and feature/layer expert knowledge. Each audited surface receives consistent smallest-target guidance or an explicit `N/A` reason in the agent plan. Discovered implementation gaps that remain unfixed receive `doc/08_tracking/bug/` records with precise location and unblock condition.

## Rollback

Wire/schema changes are additive within v1 or use a new major. Provider activation retains the previous generation until candidate admission succeeds. Cache namespaces are retained. Catalog migration can temporarily use an explicit legacy importer, but rollback must not restore multiple silent authorities.
