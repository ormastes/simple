# Item 4 parallel ownership

## Mach-O legacy reexport continuation (2026-10-04)

Base: `487d64cfac314787e89c8bb7304e0a24eae3d450`, target `release/1.0`.
Root owns integration, the no-closure hosted guard, verification report and
final review/merge. Runtime owns provider metadata, validating binary projection
and actual closure selector/inference integration. Acceptance owns real binary
fixtures, `item4_macho_legacy_reexport_spec.spl` and its authored manual. Research
owns the legacy detail design, SDK/host progress plans and independent exact
source/test review. Each lane uses its own clean worktree and fresh branch;
lower-model sidecars N/A. Initial test intent `bf0ff4730f8` precedes production.

Additive provider metadata: `sub_umbrellas`, `sub_libraries`,
`no_reexported_dylibs`, `infer_subframeworks`; defaults preserve existing callers.
The detail design freezes matching all ordinary/weak dependency records,
unmatched no-ops, header suppression and old-format-only subframework inference.
Test helpers use `item4_macho_legacy_` and canonical `std.spec.step`, actual
production calls, guarded fixture mutations and independent output assertions.
Simple execution remains UNRUN; source review does not complete SDK or host gates.

## 2026-10-04 ELF byte-source continuation

Base: `d945e61704c7baeca8fe354eb812e390b156a561`, target `release/1.0`.
Root integrates on `work/item4-elf-byte-source-20261004` and owns the freestanding
adapter, common plans/report, final review and merge. Runtime owns the operation
binding extension and hosted `_LinkerWrapper/native_linking.spl` integration.
Acceptance owns executable specs, fixtures and authored manuals. Research owns
design and independent review. Agents create separate worktrees at this base;
root reuses its clean integration worktree. Lower-model sidecars: N/A.

Keep the three-facet array-input APIs unchanged. New file APIs are
`elf_builtin_file_operation_providers_v1`, `elf_builtin_file_operations_v1`,
`elf_seal_file_operations_v1`, `has_byte_source`, `read_bytes`,
`link_freestanding_with_operations_v1`, and
`internal_link_native_with_operations`. Test helpers use `item4_elf_source_`
and `std.spec.step`. Concrete test intent precedes implementation.

## 2026-10-04 static ELF operational composition continuation

Base: `80b5ab3f6f568bd614f28a4c91244713a2bb9381`, target `release/1.0`.
Root integrates in `C:/dev/simple-item4-sha-owner-20261004` on
`work/item4-elf-operations-20261004` and owns common plans, verification report,
final review and merge. Runtime owns the new leaf operation-binding module and
the existing static-link driver. Acceptance owns executable specs and authored
manuals. Research owns design/research documents and independent source review.
Each agent uses a newly isolated worktree and session record at the same base.

Shared types: `ElfOperationProviderV1`, `ElfSealedOperationsV1`,
`ElfComposedImageV1`. Entry points: `elf_seal_operations_v1`,
`elf_builtin_operations_v1`, and `elf_link_with_operations`. Tests use
`item4_elf_ops_` helper names and `std.spec.step`; runtime waits for test intent
before implementation. Lower-model sidecars: N/A. Structural receipts never
stand in for runtime execution, trusted manifest admission or resource evidence.

## 2026-10-04 RV64 initial-exec TLS continuation

Base: `75076715f57c7c9f20e98019a4a9ec5b1bdc0d0d`, target `release/1.0`.
Root integrates on `work/item4-riscv-ie-20261004`, owns common plans and the
verification report, and is final merge reviewer. Acceptance owns test-first
full-link SSpec, assembly/object fixtures and authored manual in a new isolated
worktree. Runtime owns relocation classification, high/low pairing and the
existing static linker path in another new isolated worktree. Research owns
psABI research, detail design and independent source review in a third worktree.
All lanes start from the same base and record their session bindings.

No new public schema or callback interface is required. Private test helpers use
`item4_riscv_ie_`; scenario steps use `std.spec.step`. Tests must assert real
linked bytes against independent ABI expectations. Missing runtime evidence is
UNRUN, never a placeholder pass. Lower-model sidecars: N/A.

## 2026-10-04 terminal shutdown continuation

Base: `8e141ae45a89250f30f694e49cd0312ac3eafa10`, target `release/1.0`.
Root integrates on `work/item4-provider-shutdown-20261004` in the existing
clean `C:/dev/simple-item4-sha-owner-20261004` worktree and owns the readiness
ledger, verification report, review and merge. Separate worktree lanes:

- Research: `C:/dev/simple-item4-generation-spec-20261004`; four test-first
  retirement scenarios, design/manual, independent core and acceptance review.
- Acceptance: `C:/dev/simple-item4-shutdown-tests-20261004`; two real mapped
  shutdown scenarios and terminal cleanup of the six existing positives.
- Runtime: `C:/dev/simple-item4-shutdown-core-20261004`; generation retirement
  and lifecycle shutdown, after both test intents were committed.

Shared APIs are `retire_active(expected)`, `shutdown()`, `is_closing()` and
`is_closed()`. Lower-model sidecars: N/A. Root is final integration reviewer.
Runtime tests and canonical docgen remain UNRUN; source review is not admission.

## 2026-10-04 configured provider continuation

Base: release `b0f0cf98787`. Root owns lifecycle configured dispatch and final
integration on `work/item4-provider-positive-20261004` in its isolated worktree.
Runtime owns versioned native-config transport, command dispatch and mapped-pack
invocation in a separate worktree. Research owns transport specs before source,
design and independent source review. Acceptance owns six real mapped-provider
positive scenarios and fixture bytes in another worktree. Sidecars: N/A.

Shared API: `LinkerPackJobV2` with request, policy, inputs, output and
native_config; `linker_pack_encode_job_v2`/`decode_job_v2`; pack
`invoke_with_config`; lifecycle `run_with_config` and `run_recovery_with_config`
take config last. Configured static callbacks take config last and forward to
the native adapter's existing config-third signature. Test helpers use
`item4_pack_positive_*`, actual provider artifacts and independent ELF/exit
oracles. Missing prerequisites fail by name; no mock mapping or canned success.

Production CLI routing and trusted manifest authority remain separate open
requirements. The config-preserving transport and positive native cases are
prerequisites, not substitutes for those requirements or full Phase 4 evidence.

## 2026-10-04 canonical stream continuation

Base: release `d8680fe6ec21`. Root integrates in its existing clean isolated
worktree on new `work/item4-semantic-owner-20261004`; separate registered
worktrees hold runtime/core, acceptance/spec and research/caller audit work.
Runtime owns the canonical stream module; acceptance writes regression intent
before implementation and reviews core; research audits actual callers and
independently reviews ownership transitions. Root owns final design/manuals,
integration and merge. Lower-model sidecars: N/A.

Agreed interface: mutating public operations retain their full names as `me`
methods without a stream parameter; constructors and observers remain free.
No issuer activation: actual-call audit found no production caller outside the
primitive. Its future capability boundary remains deliberately unavailable.

## 2026-10-04 SHA dependency continuation

Base: `f5fec9ccf8cb` on release/1.0. Root integrates in isolated
`C:/dev/simple-item4-sha-owner-20261004`, branch `work/item4-sha-owner-20261004`.
Runtime owns core SHA methods and regression intent in its separate sha-core
worktree; acceptance owns independent source/vector review; research owns the
provider-positive design supplement and outer semantic-stream defect report in
its separate provider-docs worktree. Root owns caller migration, documentation,
merge and final status. Lower-model sidecars: N/A.

Shared API agreed before coding: constructor `sha256_stream_v1_new`, mutable
`reset`, `update`, `update_byte`, `finish_hex`, `zeroize`; private mutable
compression and byte-push. Tests use actual owners and fixed digest oracles.
No admitted runtime exists in current evidence. Native tests/docgen/coverage
and full Phase 4 remain UNRUN/FAIL; no passing placeholder replaces them.

Date: 2026-10-03. Initial inspection base and target at allocation:
`e9cd3153c881c55f59eaaa2573b4b8a5e803023a` (`origin/release/1.0`).

Private lanes refreshed to `cb2f783acf0ea22e8da54ff0d8d18b4fb14c816c` before
integration. The intervening change affects the frontend flat-pool codec and
its two tests; inspected linker sources and the research document are unchanged.
Session metadata records this refreshed base/expected target. No runtime PASS
evidence exists to transfer across the rebase.

## Test-first continuation

On the user's `codingtest first` instruction, the same isolated worktrees are
reused with new exclusive ownership: `/root` strengthens the existing image
acceptance spec and updates plan/design; `/root/linker_acceptance` owns the new
`item4_linker_relocation_acceptance_spec.spl`; `/root/linker_research` owns the
new `item4_linker_dynamic_acceptance_spec.spl`; `/root/linker_runtime` reviews
the image assertions read-only. All three specs live under
`test/03_system/app/compiler/feature/`. Helper prefixes are `item4_reloc_` and
`item4_dynamic_` for the new files. Root's image helpers are `item4_read_le`,
`item4_check_elf_load_segments` and `item4_pe_file_offset`.

This ownership amendment applies to this test-first wave; the original lane
table below records the completed research/initial-spec allocation. Runtime
execution and production fixes remain separate pending work.

## Implementation continuation ownership

On `go impl`, `/root` owns ELF parser bounds and its new input-bounds spec;
`/root/linker_research` owns shared-object DT_NULL/string termination and the
dynamic spec; `/root/linker_acceptance` owns the typed native-link result,
wrapper/adapter threading and engine-receipt spec. `/root/linker_runtime` runs
bounded diagnostics in the integration worktree's `build/item4-diagnostic/`
and canonical `build/scv` cache, without editing production files. Root's probe
source is `test/fixtures/linker/diagnostic/item4_linker_probe.spl`.
Research independently reviewed result threading; runtime independently reviewed
the parser bounds. All reviews are source-only unless actual execution receipts
are explicitly attached. The three-attempt diagnostic cap remains in effect.

| Lane / owner | Isolated worktree and work branch | Exclusive edits |
|---|---|---|
| Integration / `/root` | `C:/dev/simple-item4-linker-dev-20261003`; `work/item4-linker-dev-20261003` | Plan/design, acceptance plan, lane ledger, subsequent reviewed production fix |
| Research / `/root/linker_research` | `C:/dev/simple-item4-linker-research-20261003`; `work/item4-linker-research-20261003` | Dated addendum to linker research |
| Acceptance / `/root/linker_acceptance` | `C:/dev/simple-item4-linker-acceptance-20261003`; `work/item4-linker-acceptance-20261003` | New item4 system acceptance spec |
| Runtime reconnaissance / `/root/linker_runtime` | Read-only existing environment; no work branch | No edits or interference with live bootstrap |

All coding agents use the inherited model; no lower-model sidecars are used.
Merge owner: `/root`. Final review owner: `/root` plus an independent same-model
agent after integration; reviewer must inspect the exact final diff and actual
RED/GREEN evidence. No reviewer is assigned to certify unexecuted tests.

Shared requirement IDs are ITEM4-REQ-001 through ITEM4-REQ-010 in
`doc/03_plan/sys_test/item4_linker_acceptance_2026-10-03.md`. Shared helpers are
`item4_load_elf_fixture`, `item4_static_link_error`, and
`item4_archive_with_member_type`; use canonical `std.spec.step`. Missing setup
or unsupported evidence must fail explicitly, never pass a placeholder.

Research commits are integrated before plan reconciliation; acceptance commits
precede production fixes. Each owner reports its exact commit and tests run.
Only owned commits enter the release-targeted integration branch. Existing
main-worktree dirty command files and other item1/item5/bootstrap worktrees
remain outside this change. Refresh the expected target before submission and
renew evidence affected by any rebase. Release refs move only through reviewed
PR integration; this task does not authorize release tags or publication.

## Completion coding wave ownership (2026-10-03)

Root's new branch is `work/item4-linker-completion-20261003` in the existing
integration worktree. Root owns configured request admission, PE routing and
facade/receipt specs. Acceptance owns RISC-V pair evaluation/patching and its new
spec on `work/item4-riscv-relocations-20261003`. Research owns linker lifecycle
and its new spec on `work/item4-linker-lifecycle-20261003`. Runtime reviews root's
routing and revalidates runtime availability read-only. All use the inherited
model. Root integrates exact commits and reviews source; no runtime PASS or full
item 4 completion is authorized by source review. Remaining source owners are
listed in the acceptance plan rather than relabeled as missing evidence only.

## Full coding continuation ownership (2026-10-03)

Root integrates on `work/item4-full-linker-20261003`, owning hosted FreeBSD,
explicit freestanding file dispatch, publication and documentation. Acceptance
owns RV64 static-driver, ULEB and alignment work in its existing isolated
worktree. Research owns retained spill/file reading and section emission on
`work/item4-linker-bounded-20261003`; it also performs independent integrated
source review. Runtime owns Mach-O static construction and dylib-reading work
in `C:/dev/simple-item4-macho-20261003`, `work/item4-macho-20261003`.

All agents use the inherited model; lower-model sidecars are N/A. Tests are
committed before the corresponding implementation. Root reviews agent source;
acceptance reviews root's hosted/adapter changes and research reviews integrated
Mach-O/adapter changes. Root is the merge owner. Runtime tests, generated-manual
validation and coverage are UNRUN, so source review cannot award verify PASS.
The prior three-attempt runtime diagnostic cap is unchanged.

## Verification readiness continuation (2026-10-03)

The user requests remaining items be divided into implementation and test work
before Phase 4. The authoritative current breakdown is
`doc/03_plan/compiler/linker/item4_verification_readiness.md`.
Root integrates on `work/item4-verification-readiness-20261003`, owns provider
lifecycle binding and common documents. Research owns retained archive/bounded
execution in its original isolated research worktree. Runtime owns hosted Mach-O
in the Mach-O worktree. Acceptance owns remaining RISC-V work in the acceptance
worktree. All start from release `94a16103a5baeefad8bc7688e70b43b75dcf2914`.
No agent edits another lane. Tests precede implementation, root reviews source,
and an independent inherited-model agent reviews root. Lower-model sidecars N/A.

## Historical main forward-port (before branch reconciliation)

The following note describes the earlier main-only adaptation. The reconciled
tree retains the newer release strict authority and configured-linker owners.

### Main forward-port of release PR #2294 (2026-10-03)

The shared ELF admission and executed-engine fixes landed on `release/1.0` in
`7d16ab11d2227cbe5f29dc998b76a1eff326abbb`. The targeted main forward-port
preserves main's existing admission behavior: main lacks the release-only
strict tool/runtime authority modules, so its typed result wraps the existing
entrypoint directly, and the fallback spec omits that unavailable import/check.
All other production guards and acceptance scenarios are carried forward.
Runtime SSpec, generated-manual, coverage and core/MCP evidence remain unrun;
this forward-port does not change any requirement's verification status.

## Bounded COMMON implementation ownership (2026-10-04)

Base and expected release target: `63d5f8b20208c92275cfb4c9a105a26b2b51b774`.
Root integrates on `work/item4-stream-common-20261004` in
`C:/dev/simple-item4-sha-owner-20261004`, owning shared plans, evidence and merge.
Runtime owns stream_inputs/layout/emit in the separate
`simple-item4-stream-common-core-20261004` worktree; acceptance owns the new
`item4_stream_common_spec.spl`, its manual and real fixtures in
`simple-item4-stream-common-tests-20261004`; research owns the design and
provider-authority findings in `simple-item4-stream-common-docs-20261004`.
All child worktrees are under `C:/dev/`, on matching `work/*` branches.

Shared public link API and layout fields remain unchanged. New helpers use
`elf_stream_common_*` for production and `item4_stream_common_*` in specs.
Use real setup/checker assertions and fail immediately on missing prerequisites.
Acceptance commits test intent before runtime implementation starts. Root and
research review final source/test behavior. Lower-model sidecars: N/A; inherited
models retained. No admitted runtime exists in this lane; authored tests remain
UNRUN and cannot establish TDD RED/GREEN, coverage or Phase 4 PASS.

## Ordinary static x64 GOT ownership (2026-10-04)

Base/expected release target: `11a5ade180d895de65342ed983ce34ad06506a33`.
Root owns integration, common plans and merge on `work/item4-stream-got-20261004`
in `C:/dev/simple-item4-sha-owner-20261004`. Separate child worktrees under
`C:/dev/` are `simple-item4-stream-got-core-20261004`,
`simple-item4-stream-got-tests-20261004`, and
`simple-item4-stream-got-docs-20261004`, each on its matching `work/*` branch.
Runtime owns stream_got and stream_inputs/layout/emit; acceptance owns the
new item4_stream_got spec/manual and actual fixtures; research owns design,
primary ABI research, external fixture experiments and independent review.

Public stream link/layout contracts remain unchanged. Production helpers use
`elf_stream_got_*`, test setup/checkers use `item4_stream_got_*` with real
assertions and explicit setup failures. Slot identity is tagged global name or
local owner/table/ordinal; payload is the resolved address, never address plus
relocation addend. GOT base follows COMMON, independent of slot contents. The
ordinary types are 3,9,25,26,27,28,29,30,31,41,42,43. TLS/dynamic work stays open.
Test intent precedes implementation. Root and research review exact changes;
lower-model sidecars N/A. No admitted runtime or RED/GREEN execution is claimed.

## ELF COMDAT implementation ownership (2026-10-04)

Base/expected release target: `07c4fb746ccbdd06be1934662cc5dcad9b7b4046`.
Root integrates on `work/item4-stream-comdat-20261004` in the existing isolated
`C:/dev/simple-item4-sha-owner-20261004` worktree. Child agents reuse their own
clean GOT core/tests/docs worktrees on new matching `work/item4-stream-comdat-*`
branches. Sparse unrelated root deletions remain outside their source commits.
Runtime owns ELF group reading and stream input/layout/GOT/emission integration;
acceptance owns `item4_stream_comdat_spec.spl`, fixtures and manual; research owns
ABI/GNU experiments, design and independent source review. Root owns plans,
reports, final review and the release-branch PR. Lower-model sidecars: N/A.

Shared public methods on `ElfStreamInputsV1` are
`elf_stream_comdat_validate_v1(object, cancelled)` and
`elf_stream_comdat_section_kept_v1(owner, index, cancelled)`, returning
`Result<bool, text>`. Existing public link/layout APIs remain unchanged.
Test helpers use `item4_stream_comdat_*` and `std.spec.step`, real setup assertions
and explicit failures. Initial executable intent precedes production edits.
Undefined symbol archive demand follows the GNU experiment, while final errors
follow surviving allocated references. No runtime RED/GREEN or coverage is
claimed without an admitted self-hosted executable.

## Resource evidence and worker ownership (2026-10-04)

Root integrates `work/item4-resource-evidence-20261004` in the existing isolated
root worktree from release base d11536cc67be20934752b566f63e2bb10ccfe7ee.
Child agents reuse their own prior clean core/test/doc worktrees on matching
`work/item4-resource-evidence-*` branches with new session records. Root owns
link_accounting.spl, common plans, opt-in linker guide, review and merge; runtime
owns the production resource_scope.spl observation path; acceptance owns
classifier and real-file observation specs/manuals; research owns primary-source
worker design and independent review. Sidecars N/A. Test intent precedes fixes.

Shared production test seam: resource_scope_systemd_metrics_v1(show_output,
exit_code, runtime_error, stdout_truncated, stderr_truncated), returning
Option<(peak_bytes, cpu_ns)> from the actual systemd observation caller. Tests
use item4_resource_evidence_* helper prefixes, std.spec.step and real assertions.
Measurement-only APIs must not manufacture QualifiedJobScope. Missing or invalid
peak files/properties must remain unavailable. The full worker's before-exec
limits, no-swap, descendant ownership and parent-authoritative publication remain
separate implementation obligations. All Simple tests remain UNRUN.

User selection: the mold-style Simple linker stays accessible through explicit
SIMPLE_LINKER=internal and is not made the default hosted linker.

## Private stream preparation ownership (2026-10-04)

Base/expected target: 02e4836a820507d8bdf38f1feea31c44c649ee92, release/1.0.
Root integrates work/item4-stream-prepare-20261004 in the existing isolated root
worktree. Child agents reuse their clean prior core/test/doc worktrees on new
work/item4-stream-prepare-* branches and session records. Runtime owns
stream_link.spl; acceptance owns item4_stream_prepare_spec.spl and its manual;
research owns design and independent review. Root owns host matrix, shared plans,
reports and final merge. Lower-model sidecars: N/A.

Frozen API: elf_stream_prepare_file_v1 has no destination argument and returns
ElfStreamPreparedV1 with optional stage, directory and publication_attempted.
Its me elf_stream_publish_prepared_v1 transfers remaining cleanup ownership to
the existing ElfStreamLinkResultV1 on success and clears prepared ownership.
Every publication or discard attempt retires publication permission before work;
cleanup retries remain available. me elf_stream_discard_prepared_v1 independently
cleans retained components and is idempotent when empty. Existing one-shot linking
uses this real path, preserving early output validation, logical quotas and
no-clobber publication. Helpers use item4_stream_prepare_* and std.spec.step with
real assertions. Test intent 623186e2f83 preceded implementation. Runtime UNRUN.

## macOS native facade ownership (2026-10-04)

Base: 4da06603013a468071da66824a933051a4c10b07, target release/1.0.
Root integrates work/item4-macos-facade-20261004 in its isolated worktree.
Runtime owns native configuration extraction, Mach-O file adapter, wrapper and
request dispatch; acceptance owns item4_macos_native_spec and its mirrored
manual; research owns macos_native_facade design and independent final review.
Each child uses its own clean worktree and feature branch. Root owns shared
plans, verification report and final PR review/merge. Lower-model sidecars: N/A.

Shared interfaces: MachONativePlanV1, native_macho_plan_v1(arch,config,output),
native_macho_link_files_v1(plan,object_files,runtime_archives,output). Move the
unchanged NativeLinkConfig/default to an acyclic module, preserving existing
wrapper exports. Production performs real host/admission/runtime resolution;
the same file adapter permits fixture-based cross-format evidence without
pretending the fixture runner is Darwin. Tests use item4_macos_native_* helpers
and real std.spec.step assertions. No silent setup or placeholder passes.

Native image publication retains its existing replacement behavior, distinct
from the streamed no-clobber API. Planning/construction failure must preserve
an existing destination. Explicit SDK/platform versions and modeled flags are
required; unsupported configuration and .tbd/cache providers fail explicitly.
External default and managed internal-admission refusal remain intact. This
adapter does not close missing SDK providers, Mach-O semantics, native Darwin
execution or any other host gate. Simple execution remains UNRUN.

## Mach-O duplicate policy ownership (2026-10-04)

Base: fb54131d4092053c0850ae3337fea5bde17853eb, target release/1.0.
Root owns integration branch work/item4-macho-duplicates-20261004, plans, guide,
verification report and final merge. Runtime owns symbols.spl, hosted_link.spl
and native_adapter.spl. Acceptance owns real fixture variants, duplicate-policy
SSpec and mirrored manual. Research owns the policy design and independent final
source/test review. All agents use their own clean worktrees; sidecars N/A.

Frozen interfaces: MachOHostedRequest.allow_duplicate_definitions defaults false;
macho_definitions and macho_unresolved accept the same optional false policy.
Hosted archive fixed-point scans and final definitions both consume that field.
The adapter forwards the real NativeLinkConfig value. True retains the first
selected strong definition; false preserves duplicate failure. Existing Mach-O
defined-strong, defined-weak, common precedence and common layout remain intact.
Existing static/default-hosted callers retain strict behavior.

Test helpers use item4_macho_duplicates_* and shared steps: Select strict or
first-definition policy; Link real competing definitions; Inspect the selected
definition in emitted bytes; Preserve the destination on strict rejection;
Remove owned fixture files. Initial test intent must precede implementation.
Weak/common resolver assertions do not establish hosted weak-coalescing support.
SDK providers, managed admission and actual native host execution remain open.

## Typed Mach-O providers and full SDK dependency plan (2026-10-04)

Base: 44b0d32606481ce7daf2d1971b0a973b5d065e60, target release/1.0.
Root integrates work/item4-macho-providers-20261004 and owns shared plans,
verification and merge. Runtime owns provider_types.spl, binary_provider.spl,
hosted_link.spl, hosted_fixups.spl and hosted_image.spl. Acceptance owns the typed
provider spec/manual and any scoped fixtures. Research owns full SDK design and
independent exact source/acceptance review. Separate clean worktrees; sidecars N/A.

Frozen API and types are recorded in macho_sdk_providers_2026-10-04.md. The
actual hosted consumer accepts address-free MachOProviderV1 metadata; the old
byte API calls the real binary reader before projection. Optional version
absence is preserved. Client and umbrella declarations are retained but refused
by hosted linking until actual access binding exists. Existing selected-export
unsupported gates remain; unused weak/reexport metadata and resolver flags must
not be erased or needlessly rejected.

Helpers use item4_macho_provider_* with shared steps: Read a real binary provider
through its validating reader; Link through the shared typed provider path;
Inspect provider metadata and emitted bindings; Reject invalid metadata before
publication; Preserve unsupported provider semantics. Initial executable intent
precedes source changes. The four-stage SDK plan remains mandatory; this seam
alone does not satisfy either text format, dependency closure or native execution.

## SDK text-stub readers and real file routing (2026-10-04)

Base: e1495a1e9dd4a8a224e24da2f3e2d21c11652d4d, target release/1.0.
Root owns work/item4-macho-text-stubs-20261004, native_adapter.spl, shared
tracking and integration. Runtime owns new tbd_* source modules; acceptance
owns TextAPI fixtures, executable specifications and manual; research owns
reader design and independent final source/test review. Separate worktrees;
sidecars N/A. Initial fixture/adapter intent bc11b811906 precedes adapter source;
reader intent ca8bf6a6374 precedes reader implementation. No RED execution is
claimed without the admitted runtime.

The frozen reader returns target-selected semantic documents, retaining scoped
install identities and unsupported semantic metadata. Both v4 and v5 are
required. Leaf lowering explicitly rejects unresolved dependency/access and
other unsupported semantics instead of erasing them. The native adapter reads
selected .tbd files through this reader and lowerer into the actual typed hosted
engine, preserving library selection and destination preservation on error.

Helpers use item4_macho_tbd_*; shared steps include Plan an explicitly selected
Mach-O link; Link real object and provider files; Inspect the published Mach-O
commands and bytes; Preserve the destination on selected-provider failure;
Remove owned fixture files. Reader/schema, resource-limit, metadata, TLV and
Objective-C assertions complement actual file-route checks. LLVM fixture
validation is independent syntax/metadata evidence, not Simple execution.
Full SDK closure, binding, discovery and all-five-host execution remain open.

## Mach-O provider graph and SDK resolution (2026-10-04)

Base: 9f4a7c01a0dbe2cd0bb83b9bc4980ad1cbf126e5, target release/1.0.
Root owns work/item4-macho-sdk-closure-20261004, native adapter/search modules,
shared tracking and landing. Runtime owns closure types/source/graph, shared
TBD lowering and hosted lookup integration. Acceptance owns real closure/alias
fixtures and specifications/manuals. Research owns closure detail design and
independent final source/test review. Separate worktrees; sidecars N/A.

Initial real SDK-chain intent 865f0a73251 precedes implementation. The graph
retains direct roots and dependency edges; imports preserve original outward
names and direct root ordinals. Client restrictions apply to direct providers
using actual output identity or explicit -client_name, never signing identity.
Root's loader callback uses explicit SDK/search paths and requester provenance.
It cannot silently select another provider after a chosen file fails validation.

Helpers use item4_macho_closure_*; shared steps cover Construct a real SDK
dependency tree; Resolve inline and external providers; Inspect direct load
commands and outward bindings; Enforce direct client restrictions; Preserve
the destination on closure failure; Remove owned fixture files. Cycles and
aliases require bounded pair-aware lookup. Both architectures/formats, missing
and ambiguous identities, actual access outcomes and budgets need assertions.
No executed RED/GREEN, runtime coverage or host qualification is inferred from
authored intent and independent external fixture inspection.

## Native test generated-source authority repair (2026-10-04)

Base: `9af9a8c0c70c4a04f6fc3a5bac7db475362854f5`, target release/1.0.
This pending prerequisite follows the independent loader-helper recovery; it
does not mark item4 or the test harness verified. See the
[acceptance obligations](../sys_test/item4_linker_acceptance_2026-10-03.md#native-test-generated-source-authority-prerequisite-2026-10-04)
and [detail design](../../05_design/compiler/linker/native_test_generated_source_authority_2026-10-04.md).

| Owner | Exclusive work |
|---|---|
| Runtime agent | New `src/lib/nogc_sync_mut/test_runner/native_test_source_stage.spl`; native integration in `test_runner_execute.spl`; coordinator parsing/admission in `src/app/cli/native_build_main.spl` |
| Acceptance agent | `test/01_unit/lib/test_runner_native_source_authority_spec.spl`, its mirrored manual, and coordinated native-backend integration fixture corrections |
| Research agent | Pending detail design and canonical plan linkage; independent source/test review |
| Root | Integration, shared status/evidence, exact-head final review and landing |

Separate isolated worktrees preserve ownership. Sidecars: N/A. Initial executable
intent `b83b2acb980` precedes implementation; no observed RED/GREEN is claimed.
Helpers use `item4_native_authority_*`. Shared steps are: Transform a genuine spec
suffix through the production wrapper; Stage generated bytes under checkout
authority; Retain then remove only owned generated artifacts; Parse the actual
coordinator authority request; Construct compile arguments for the staged entry.

Frozen staging API: `NativeTestSourceStageV1{directory, path}`;
`native_test_stage_source_v1(checkout_root, source_path)` returns a checked stage
or error; `native_test_cleanup_source_v1(stage, keep_artifacts)` reports cleanup
success without recursive deletion or removal of unrelated files. Native paths
stage the preprocessed source; the original SMF path stays unchanged. Cleanup
occurs after terminal compilation, preserving its primary error and retaining
artifacts when requested.

Frozen coordinator API: `NativeBuildAuthorityRequestV1{args, refresh}` and
`native_build_authority_request_v1(args, internal_worker)`. Only an explicitly
requested coordinator clears/acquires/publishes authority; duplicate flags and
worker refresh requests reject. Downstream arguments omit the refresh flag;
workers inherit the acquired generation. The parent test runner must not mutate
its own SCV environment. Coverage and explicit AOT omit the restricted source
list and use canonical default roots. Runtime execution, fresh-generation
integration and all original item4 release gates remain UNRUN/open.

Source candidate `44d01e5fbcb` implements the three owned production paths.
Five staging/parser/argv unit scenarios and root's one real Git snapshot
scenario (`a86230d1301`, manual `9ce30feac71`) are authored, all UNRUN.
The root snapshot test covers real acquire and immutable generations without
publishing bindings; it is not CLI refresh or child-isolation evidence.
Compilation uses the existing owned-test route: an explicit unreaped-tree
receipt retains artifacts and fails, while providers without a receipt retain
their synchronous contract without a universal tree-reaping claim. Root's
remaining backend fixture checks distinguish assertion failure from a plain
`fn main` zero-example rejection; the latter is not a compile-negative oracle.

## Hosted ARM64 ADDEND owner split (2026-10-04)

Base `edfb6df1821ff98a0d563cca5496630cedf7789e`, target release/1.0.
Runtime owns `macho/relocation_pairs.spl`, `relocations.spl` and
`hosted_fixups.spl`; acceptance owns real ARM64 fixtures, executable acceptance
and its mirrored manual. Research owns local/domain research, detail design,
plan linkage and independent source/test review. Root owns integration and final
exact-head review. Separate worktrees; sidecars N/A; tests before production.

Frozen shared API: `MachORelocationPairV1(relocation,explicit_addend,consumed)`
and `macho_relocation_pair_v1(relocations,index,arm,input_name:text)`.
Both consumers must validate/consume the same prefix and follower. Reject dual
nonzero explicit/embedded addends; preserve zero-prefix support and the existing
imported nonzero-branch refusal. Pair occupancy is counted once. This remains
existing REQ004/006 scope, not a separate user-selected requirement. Source and
runtime statuses are tracked in the linked ADDEND design; no PASS is inferred
from authored specs or independent LLVM fixture inspection.
