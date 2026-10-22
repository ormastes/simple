> Merge candidate status (2026-10-11): **UNRUN**. This resolution combines local
> `ddff8671e8348a89ab2eed285311a3ffc1809358` and remote
> `3aa33b9f8de7897fcf4e83c42bc3c44d28782cef`. All counts and PASS statements below
> retain their historical component/source-stage scope. They are not execution,
> semantic verification, or admission evidence for this combined source.

# Traceability, SDN evidence, admission and Slop implementation plan

Status: selected full-scope design and WP1 shared SDN scalar/strict component
implementation in progress. Actual Phase2 native TDD evidence exists; typed
families, CLI and all downstream work remain open.
Source: `a9777ac75fa5d64c6741de8981a9d13815990179`.
Session: `.simple/traceability_session.sdn`; branch
`work/traceability-sdn-slop-20261010`; target `origin/main` at that source SHA.
Merge owner: Codex root. Final reviewer: Astra (`gpt-6-astra`, high effort).
Lower-model implementation sidecars: N/A. Astra review does not own source edits.

## Delivery lanes and gates

| Lane | Owner / dependencies | Deliverables | Completion evidence | Current state |
|---|---|---|---|---|
| WP0 baseline | Root; none | Pin code/settings, toolchain/source provenance, hook paths, resource baseline | Admitted general-tool runtime; actual baseline/route measurements | Source inventory done; user-authorized Phase2 component execution available; general runtime admission open; release rules queried |
| WP1 model/SDN | Root; WP0 execution gate | Typed shared contracts and SDN codec; replace JSON flags/callers/tests | AC001–002; round-trip/reject fixtures; source-matched CLI | Scalar/strict component evidence and typed qualification-summary TDD recorded by source stage; full families/CLI open |
| WP2 extraction | Root; WP1 | Owned live metadata, tracking DB, conventional/irregular claims, provenance/dependencies | AC003–009 and real production feature graph | Planned |
| WP3 admission | Root; WP2 | Exact snapshot providers/cache, existing dispatcher and trusted remote authority | AC010–020/028/038; exact Git/jj/SJ routes and hostile candidates | Planned; remote trust/configuration not assumed |
| WP4 runner | Root; WP1 | Extend sole RunnerTestDb writer, run planning/attempts/finalization, real SDN import and admitted evidence; authorized completion transaction and later-input invalidation | AC021–027/039; failed/partial actual feature run; lifecycle authorization sabotage | Planned |
| WP5 projections | Root; WP2/3/4 | Shared projection; stable pages, run reports, safe offline HTML and ownership manifest | AC029–032/040; deterministic bytes and artifact agreement | Planned |
| WP6 Slop | Root; WP5 | Three-pane MDSOC tree/graph/details, historical source, keyboard/delta state | AC033–037/040; actual user interactions | Planned |
| WP7 extensions | Root; WP6 | Architecture/design/dependency projections; approved future data adapters | Shared IDs/read authority; no alternate evaluator; adapter qualification | Planned; optional external publication separately authorized |

## TDD and modern SSpec sequence

1. Select a general-tool runtime with digest and source/producer receipts into an
   isolated cache/output scope. The user explicitly permits a Phase2-derived
   development CLI/runner; retain this stage label. Rust seed use is exclusively
   bootstrap construction, never app-test execution or release qualification.
2. Run the new CLI acceptance contracts against unchanged production code and
   retain observed failing output (RED). Replace the obsolete JSON-success
   integration expectation; retain unrelated rule tests.
3. Implement SDN option parsing/result serialization through the existing codec,
   preserve meaningful legacy rule diagnostics and explicitly name worktree scope.
   Run the changed focused contracts once (GREEN); fix only actual failures.
4. Add codec schema unit/rejection cases before graph contracts, then extraction,
   exact snapshots, trusted remote sabotage, runner evidence, incremental/full
   equivalence and projections/viewer in report dependency order.
5. Each acceptance scenario has explicit REQ/AC metadata, readable `step(...)`
   workflow, real production oracle and bounded isolated fixtures. Generated
   manuals retain that narrative and show actual captures; scaffold helpers fail.
6. Astra reviews design before implementation and final source/manuals/coverage
   before verified handoff. All 40 acceptance cases and selected NFRs must be
   evidenced at their declared scope, including supported-host/remote results.

Existing green checks are never repeated without relevant new changes. At most
three fix/verify cycles per feature session; unchanged failures stop. Store each
command's subject, binary identity, result and evidence path. Run required env
guards, core/lib/MCP smoke checks when the corresponding shared code changes.
Before any commit/sync, executable specs under `doc/06_spec` must count zero.
Only verified owned work is eligible for guarded ship handoff; no protected ref,
tag, external message, deployment or remote ruleset is changed by development.

## Current blocker and next action

The known released-path executable identifies as a Rust bootstrap seed. No
admitted Stage4 artifact was found in the checked locations. New tests have not
run; do not call static source inspection RED or mark WP1 done. Discover and
verify a source-matched admitted artifact, or use a bounded isolated bootstrap
repair lane without deploying over other sessions' binaries. Scope, architecture
and acceptance source work proceeds independently of that execution gate.

## User-authorized Phase 2 execution lane

The user subsequently authorized bootstrap or use of Phase 2 because Phase 3
is not yet available. This supersedes the local Stage4-only execution preference
for development evidence. It does not confer Phase3/4, deployment or release
qualification. A copied pure-Simple Phase2 compiler is digest-bound in
`.simple/traceability_phase2_toolchain.sdn`; its upstream record says
construction-only/Phase3 pending. Its supported CLI is native-build and SMF
compile. Three full-CLI construction attempts ended in unresolved source roots
and two timeouts; that bounded lane is stopped and its caches retained. A focused
traceability build exposed two stale method calls to a hoisted MIR helper. Source
correction and real compiler regression specifications are prepared, unexecuted.
The standalone runner failed in nine HIR modules: Astra grouped them into three
older-target/newer-producer validator incompatibilities. A source-matched Phase2
construction is now isolated in `build/native_probe/traceability-phase2`, using
the Rust seed exclusively to bootstrap corrected pure-Simple compiler sources.
The source-matched compiler probe constructed successfully (1,210 compiled,
zero failed; 323.5 seconds compile plus 10.9 seconds link), with digest
`62c9fc2906db9afa4b77ac4d5e4eb4a7d2fb78e423f3b96f308b13b07273806d`.
Its fresh HelloWorld constructed and executed successfully. The production
traceability command failed on broader MIR enum/collection/type propagation;
the standalone runner timed out (124), with a detached owned worker terminated.
Neither provides SSpec execution. This is construction-only, not canonical admission. Test/docgen tools must be built
from that producer as needed; their results remain explicitly Phase2-derived.
TDD still requires actual observed RED before production changes.

Existing Phase2 HelloWorld and the optimized scalar fixture passed construction
and execution. Neither proves the general MIR repair or traceability acceptance.
Required next checks: repaired production-command construction, actual SSpec
execution, generated manuals, then all WP0–WP7 contracts. Shared compiler edits
also require the declared compiler/lib/MCP/LSP source and runtime smoke gates.

## Final bounded compiler prerequisite cycle

Astra confirmed that newer producer source `57d83549f09b374ff9105018896843d4f8ff00e9`
contains direct fixes for typed Enum/Or pattern ownership, enum collection
payloads and missing text methods. A separate owned toolchain-only worktree
`/home/yoon/dev/simple-traceability-toolchain-20261010` freezes that revision
plus the same two scalar-helper call corrections. No upstream owner files or
unrelated commits are imported into the product branch. Its source inventory,
patch, bootstrap input hashes and logs live in `build/native_probe/traceability-phase2-final`.
This is the third and final prerequisite cycle. The Phase2 producer constructed
successfully (1,223 compiled, zero failed; 162.2 seconds total) and its fresh
HelloWorld build/run passed. Final producer SHA is
`87fbd31a5781efb18c0a5a3d6250338b76705220f8d8bb1496db85625b296bc3`,
recorded separately in `.simple/traceability_phase2_final.sdn`. Only the focused
production traceability command build failed at MIR, exit 1. Astra grouped nine
diagnostics (three repeated summaries): erased iterable I64, missing substring,
SDN Array/Dict payload mismatches and an unsupported nested literal pattern.
The old helper-method and B5b errors are absent, but no command executable or
SSpec execution exists. The [remaining compiler blocker](../../08_tracking/bug/phase2_traceability_mir_gate_2026-10-10.md)
preserves the terminal evidence. This session's retry limit is exhausted: stop
rather than initiating another rebuild. The newer
producer's stricter validation does not qualify the older runner/full-CLI closure.

## Acceptance authoring continuation

Compiler retry cap remains exhausted; no new rebuild/check was attempted. Known
external bootstrap jobs are terminal, with no usable general test runtime found.
Four shared-value SDN SSpec cases now exist for AC001 component behavior. Astra
reviewed their oracles; exact canonical bytes and every table cell are asserted.
They are NOT RUN and do not qualify the complete typed document codec.
Design now records the common encoder's top-level-only Table boundary and the
decoder's obligation to reject silently skipped malformed optional sections.
Next executable work still requires a usable authorized test runtime; full typed
family, graph, evidence, admission, projection and Slop scope remains open.

### Renewed bounded bootstrap and release landing authority

The user requested `fix`, then `bootstrap ans land impls on release branch`. A new pass permits at most three changed-source repair cycles. The isolated release-target worktree is `/home/yoon/dev/simple-traceability-release-20261010`, initially bound to `origin/release/1.0` at `d66172f8fde`. Prior failures and caches remain preserved. Bootstrap construction and focused regression evidence precede reviewed release integration. The full 20-requirement / 40-acceptance-case scope remains open; compiler prerequisite fixes do not complete product implementation.

Release-target bootstrap evidence: Phase2 compiler and exact Hello native sanity passed; standalone SSpec orchestration runner constructed. Full CLI link failed (157 undefined symbols), and traceability source/HIR startup segfaulted in parallel and serial modes. A focused native pure-Simple MIR SSpec capsule executed three real examples: ordinary immutable read PASS; both immutable-address storage cases FAIL despite no HIR/MIR diagnostics. The third diagnostic attempt confirmed missing immutable GlobalAddr/static storage; the renewed bounded pass is exhausted. Product scope remains open. See `/home/yoon/dev/simple-traceability-release-20261010/doc/09_report/traceability_release_bootstrap_2026-10-10.md`.

Release review handoff: draft PR [#2892](https://github.com/ormastes/simple/pull/2892), branch `work/traceability-release-20261010`, commit `1fe06b665ce8c5fe88fe39814509037f1aca2fe1`. Six blocking pre-push gates passed. It has not landed: two focused SSpec failures and broader runtime/admission gaps remain. No publication or product-completion claim.

### 2026-10-11 release sync: focused prerequisite repaired

The user requested syncing and landing the fixes on release. The missing successful-fold registration in `global_constants_by_id` is repaired. The final pure-Simple native Phase2 capsule reports **3 examples, 0 failures**, including canonical immutable address storage for integer/text/bool and ordinary constant return without storage. Rust was used only for bootstrap construction. Native boxed-text enum equality remains a separately recorded bug; the tests now match required variants and assert exact payloads. The renewed three-cycle pass converged and passing checks were not repeated.

Published draft PR [#2955](https://github.com/ormastes/simple/pull/2955), head `39a4cfbf06564a66cb7467dfa48976a5d0946aff`, base `7f445e481c2e2ebdff3ef7e1b0aa70a49beca45b`, branch `work/traceability-release-sync-20261011`; superseded draft #2892 is closed. Six blocking push gates and GitHub Code Idiom & Structural Ratchet Gates pass. Astra renewed exact-head high-effort local source review: PASS, P0=0, P1=0. The rebase delta changes no `src`/`test` files; source digests remain identical to the passing capsule.

**Not landed:** authenticated SPipe Self Review Admission remains missing; the current trusted workflow only offers the explicitly forbidden legacy self-attestation route. Broad compiler/lib/MCP/LSP checks remain unqualified without an admitted general-purpose runtime. No status fabrication, protected-branch bypass, version/tag publication, or full-product completion claim. The original 20 REQ-TRC / 40 AC-TRC / WP0–WP7 product scope remains open. See the release worktree report and `.simple/traceability_release_sync_handoff.json`.

### 2026-10-11 WP1 scalar TDD increment

Continued in fresh owned product branch `work/traceability-product-20261011`, worktree `/home/yoon/dev/simple-traceability-product-20261011`, source base `39a4cfbf06564a66cb7467dfa48976a5d0946aff`, expected protected release base `7f445e481c2e2ebdff3ef7e1b0aa70a49beca45b`. Carried only the 13 owned plan/design/spec/fixture artifacts; preserved the original dirty lane.

Shared SDN quote and integer scalar boundaries are repaired with actual reliable RED/GREEN: quotes 2 failed before / 3 passed after; integer overflow 3 failed before / 4 passed after. Exact variants/payloads and computed rejection flags use real built-in assertions. Initial fail-only negative PASSs are INVALIDATED by independent direct parser and SSpec controls. Astra high-effort local review accepts this narrow source change with zero P0/P1. See `doc/09_report/traceability_sdn_scalar_tdd_2026-10-11.md` and its machine receipt.

WP1 is NOT done. Next: fix/qualify native SSpec failure reporting; strengthen fail-only value oracles; add opt-in strict shared full-document consumption; implement typed `TraceQualificationV1` and remaining document families; exercise malformed optional/trailing inputs and multi-table/reference closure contracts, then production CLI migration. Neither component test group completes AC001/AC002. Keep all 20 requirements / 40 acceptance cases / WP0–WP7, full CLI route, generated-manual and broad verification obligations open.

### 2026-10-11 current release and strict WP1 increment

This update supersedes historical not-landed statuses above: compiler prerequisite
PR #2955 merged into release/1.0 at 1bdffb92d6cb646fef19c27349fe27b2b7c2f8bb.
The scalar-only seven-file change is pushed in draft PR #2956 at
ba8aab48caf5958d0671b90fcbac83c7852d128d, based on release 3bb214c30fe.
Astra exact-head local source review passes with P0=0/P1=0; broad verification
and authenticated admission remain open. Other dirty lanes are preserved.

In the owned product worktree, opt-in shared strict decoding is implemented.
Actual legacy RED8/8 preceded initial strict GREEN16/0. Astra found scalar
round-trip and quoted-key defects; separate real RED3/3 preceded grouped
correction GREEN10/0, including stronger nested payload/empty variant assertions.
The runs bind separate retained source stages and are not aggregated as one
current-source acceptance pass. Final Astra component source review passes with P0=0/P1=0; see the strict TDD report
and detailed strict grammar/resource contract. No unchanged green was rerun.

Next WP1 work is typed TraceQualificationV1 decoding/encoding, other trace/Slop
families, stable named-table family encoding and reference closure, then the
production SDN-only CLI and existing modern SSpec acceptance scenarios. Generic
syntax validity cannot grant evidence trust or verified coverage. The native
fail-only runner bug remains open; repaired or independently qualified runner
evidence is necessary for later general-tool/manual qualification. All 20/40
and WP0–WP7 obligations stay open until their own evidence exists.

### 2026-10-11 typed qualification-summary increment

Implemented shared typed summaryv1 decoding/encoding and closed family dispatch.
Actual syntax-only missing-layer RED10/10 preceded initial typed GREEN15/0.
Astra source review found output-budget defects; added regression RED6/1
preceded final grouped correction GREEN11/0. Earlier/final source snapshots are
separate, and unchanged green checks were not rerun. Final source and documentation
review passes with P0=0/P1=0. The budget case covers encoding selector/diagnostic
caps and decoding text caps; individual bidirectional coverage is not claimed.

The summary codec validates all required fields/types/enums, diagnostic snapshot
references, explicit source availability and completion/exit consistency. It
retains captured snapshots when evaluation is interrupted and treats decoded
status as untrusted data. Canonical encoding preserves repeated diagnostics,
sorts their full records and enforces input/output/resource budgets before
serialization. Raw semantic/value bridges are private. See the new qualification
design and TDD report.

This does not complete the report's full qualification family: obligation/evidence/
refusal records require explicit major2 and a provenance-preserving importer,
without silently reinterpreting summaryv1. Remaining families/graph table closure
stay open. Next is actual production CLI SDN migration and source-matched command
acceptance, followed by the original WP2–WP7 dependency sequence. Full20/40,
runner/manual/runtime/NFR and authenticated integration obligations remain open.

## CLI private increment, 2026-10-11

Implementation/merge owner: Codex root. Sidecar lanes: N/A. Final source reviewer:
Astra (P0=0/P1=0). Execution reviewer: native SSpec failure preserved; no admission.
Three-cycle cap reached with Unicode/NUL6/1. Continue only in a fresh bounded lane.
Verified scalar/strict/typed release synchronization is independent.

## Distinct fixture/provider investigation

Owner: Codex root. Sidecar lanes: N/A. Final source/oracle reviewer: Astra,
P0=0/P1=0; evidence WARN. Fixed Result fixture extraction, retained capped
historical6/1, and added native3/0 plus actual provider6/5 ->6/0. Broader graph,
runner, snapshot admission, projection/Slop and complete20/40 scopes remain next.

## Typed graph private increment — 2026-10-11

Implementation/merge owner: Codex root. Sidecar lanes: N/A. Design and final
source/oracle/evidence reviewer: Astra, P0=0/P1=0. Native actual evidence stages:
corrected baseline3/3 -> initial graph3/0; acceptance14/10 -> final14/0;
intermediate superseded construction unexecuted. Graph-family typed carriers,
strict decoding, closure and bounded canonical encoding now exist. Entire20/40
and WP0–WP7 remain authoritative. Next WP1 work is other families and explicit
common-envelope/all-family dispatch, followed by original WP2–WP7; broad runtime,
coverage/NFR/manual evidence and authenticated integration stay open.

## Document/declarations private increment — 2026-10-11

Implementation/merge owner: Codex root. Sidecar lanes: N/A. Final reviewer: Astra
(final source/oracles/evidence PASS, P0=0/P1=0). Generic dispatch supports actual
qualification-summary, graph and declarations major1. Dedicated APIs keep their
signatures; raw-value entry points independently enforce structural budgets.
Native stages4/4 ->4/0 and acceptance12/0, with affected regressions14/0,15/0,11/0.
All20REQ/40AC/WP0–WP7 remain required. Next WP1 work includes policy/run/receipt,
full qualification major2, graph diagnostics and both Slop families. Original
WP2–WP7, runtime/coverage/NFR/manual and authenticated integration remain open.

Review-derived raw-boundary repair adds verified dictionary cardinality before
keys and source-less cumulative key/header/string byte limits. Earlier12/0
acceptance and regressions remain pre-repair evidence; final raw controls5/0,
acceptance13/0 and affected graph14/0, qualification15/0, budget/order11/0
match the changed source. No whole AC, broad runtime or admission PASS follows.

## Targeted operation contract increment — 2026-10-11

Full20REQ/40AC/WP0–WP7 are unchanged. Root owns implementation/merge; sidecarsN/A;
Astra is final reviewer. Declarations major2 supplies explicit add/replace/suppress
without reinterpreting major1. Desired replacement and exact original tuple are
separate, and provenance/applicability references remain untrusted data. Native
strict-valid baseline3/3 -> initial typed3/0 and broader12/0 are distinct stages.
Actual policy authorization/stale-rule resolution AC006 remains required.
See doc/05_design/infra/traceability_link_operations_v2.md and its TDD report.

The unpublished work branch was rebased onto releasee2d56c2 with all89 prior
owned product files byte-identical (AstraPASS P0=0/P1=0). New canonical Stage2
qualification stopped before compilation at its10GB disk-space guard. Logs are
retained; no admission was emitted. Continue implementation independently while
build storage is unavailable; broad runtime and protected admission remain open.

Final operation component native acceptance14/0, affected major1 declarations13/0
and qualification15/0 match the new dispatcher stage. Empty63-node shape and
exact aggregate text boundaries are covered. This remains component evidence,
not real resolver AC006 or whole20/40 completion. Source/oracle AstraPASS P0=0/P1=0;
final evidence review PASS (10source/36artifacts reconciled).

## Conventional association kernel increment — 2026-10-11

Full20REQ/40AC/WP0–WP7 remain unchanged. Root owns implementation and merge;
sidecarsN/A; Astra is final reviewer. New pure-Simple convention owners validate
bounded supplied graph/policy facts and resolve exact registered unit, integration,
component and manual associations. They preserve corroborating origins, roles,
parameter identities, explicit exclusions and positive/negative membership.
Generator-manifest bindings are required before manual candidate recognition;
source-kind/group indexes and every node/group traversal are charged. Structural
association confers no requirement satisfaction, execution proof or eligibility.

Construction RED is an actual missing-module failure with zero executed examples.
Initial native6/0 was followed by Astra causal RED8/2 and grouped cycle2 GREEN26/0.
Astra final component/source/oracle/evidence review PASS P0=0/P1=0; no unchanged
green tests were rerun after convergence. See the conventions design, executable
modern SSpec, its host-extracted manual and TDD report. Ambiguous-input permutation
coverage validates diagnostics/lookups, not claim or generator/exclusion ordering.

Next WP2 work: actual graph extraction/byte binding, complete policy ownership,
explicit operation precedence/authority/stale rules and CLI integration. WP3
incremental/full equivalence must consume both positive and negative dependencies.
All execution evidence, qualifications, Slop surfaces and remaining plan gates
continue separately. Coverage/NFR/full core/MCP/LSP checks and admitted SPipe
manual generation remain open; no full AC/REQ done mark or runtime admission.
