# Feature: Minimal-Bootstrap Configuration-Composed Dynamic Architecture

## Raw Request

Implement the saved minimal-bootstrap, configuration-composed dynamic architecture research with parallel agents, detailed guides, higher-capability review, and updates to skills, SPipe documentation, LLM wiki/process knowledge, and other development guidance so normal feature development minimizes bootstrap work.

## Task Type

feature

## Refined Goal

Make configuration-only and provider-private feature changes build and run through an unchanged minimal core using explicit composition/provider contracts, compatibility-scoped rebuild decisions, and documented SPipe workflows that prohibit unjustified full bootstrap.

## Acceptance Criteria

- AC-1: Selected feature and NFR requirements exist for this feature slug and trace every implemented milestone to stable `REQ-NNN` identifiers; no pending option file remains.
- AC-2: Architecture, detail design, system-test plan, and agent-task plan exist and define `SimpleCompositionImageV1`, `SimpleProviderQueryV1`, `SimpleCliCommandV1`, and `SimpleAppLaunchV1`, including ownership, versioning, compatibility, security, failure, cache, invalidation, startup, latency, and RSS decisions.
- AC-3: The first executable slice accepts deterministic composition source, emits/reads a validated immutable composition representation, and proves that changing an application record does not recompile or replace the core executable.
- AC-4: A leaf CLI provider slice dispatches through the provider contract and proves that a provider-private implementation change rebuilds only the provider plus any locked composition digest projection, not the core or compiler provider.
- AC-5: Build-explain evidence reports requested target, relevant digest deltas, selected rebuild closure, cache reused/rebuilt counts, `bootstrap_required`, and a non-empty typed reason whenever bootstrap is required; unknown compatibility never authorizes reuse.
- AC-6: Executable SSpec scenarios under `test/03_system/` trace requirements and use the shared manual flow helpers `compile_composition`, `load_unchanged_core`, `dispatch_provider`, and `explain_rebuild`; incomplete scaffolds use `assert(false)` or `fail(...)`, never placeholder passes.
- AC-7: SPipe-generated/manual documentation under `doc/06_spec/` reads as an operator manual and matches executable scenarios; `find doc/06_spec -name '*_spec.spl'` returns no files.
- AC-8: Focused pure-Simple checks demonstrate deterministic output, malformed/overlap/hash rejection, binding/interface validation, provider compatibility, and rebuild containment. Each unchanged passing criterion is run at most once, with no more than three fix/verify cycles.
- AC-9: Normal feature-development guidance is updated consistently across `.codex/skills/`, `.agents/skills/`, `.claude/skills/`, `.claude/agents/spipe/`, `.claude/commands/`, `.gemini/commands/`, `doc/07_guide/`, and relevant SPipe docs, or each unaffected surface is marked `N/A` with a concrete reason. Guidance requires the smallest named target/provider/SCI projection first and full bootstrap only for a typed incompatibility or explicit release/trust target.
- AC-10: Feature- and layer-expert knowledge exists under `doc/00_llm_process/feature_expert/minimal_bootstrap_configuration_composed_dynamic_architecture/skill.md` and an appropriate `doc/00_llm_process/layer_expert/` entry; any discovered but unfixed gap has a `doc/08_tracking/bug/` record with file/line and unblock condition.
- AC-11: Higher-capability final review checks requirements traceability, architecture coherence, parallel-lane integration, generated-manual quality, exclusions, and completion evidence before verify may report PASS.
- AC-12: The implementation preserves explicit self-host convergence and DDC as release/trust targets and does not silently use the Rust seed, startup shell compilation, global cache clearing, compiler-internal objects as stable ABI, or a second launch/application manifest.

## Scope Exclusions

- The first implementation does not split lexer, parser, HIR, or MIR into independent dynamic providers.
- It does not claim cross-platform native/SMF provider parity without fresh evidence for each platform.
- It does not perform a release, version bump, tag, or push.

## Cooperative Review

- Research/design sidecars: requirements/architecture lane, implementation/target-graph lane, and documentation/wiki/process lane.
- Merge owner: root Codex agent.
- Final reviewer: a fresh highest-capability review agent after integration.
- Shared interfaces: `SimpleCompositionImageV1`, `SimpleProviderQueryV1`, `SimpleCliCommandV1`, `SimpleAppLaunchV1`.
- Manual flow helpers: `step("compile_composition")`, `step("load_unchanged_core")`, `step("dispatch_provider")`, `step("explain_rebuild")`.
- Setup/checker helpers: `setup_minimal_bootstrap_fixture`, `check_composition_image`, `check_rebuild_receipt`, `check_bootstrap_reason`.
- Fail-fast placeholder policy: incomplete helpers must call `assert(false)` or `fail(...)`.
- Generated-manual review owner: final highest-capability review agent; root remains responsible for fixes.

## Phase

dev-done

## Overall Status

implementation-in-progress

## Log

- dev: Created state file with 12 acceptance criteria (type: feature).
- docs inventory: canonical public guidance is
  `doc/07_guide/compiler/minimal_bootstrap_configuration_composition.md`;
  feature/layer expert and cross-tool workflow surfaces are in scope.
- docs N/A: private overlay trees `.spipe/00_llm_process/`,
  `.spipe/10_llm_wiki/`, `.spipe/20_raw_doc/`, and `.spipe/core/` do not exist
  in this checkout, so there is no overlay material to distill or refresh.
- docs N/A: release skills are excluded because this feature does not release;
  convergence and DDC remain explicit release/trust targets.
- docs N/A: generic design skills remain unchanged because architecture and
  interface decisions live in this feature's design artifacts and canonical
  guide; adding a global design rule would duplicate feature policy.
- implementation: L1 added the deterministic SCI v1 app-record codec and
  separately buildable config compiler; L4 added a receipt value model and
  fail-closed compatibility/bootstrap-reason validation; root added validated
  launcher-byte admission and the first executable/manual SPipe pair.
- evidence limitation: the available `bin/simple` reports that it is a
  Rust-built bootstrap seed. Its exit-0 focused checks are diagnostic only and
  do not satisfy AC-8's pure-Simple evidence requirement.
- highest-capability review 1: REJECT. It found digest verification using the
  wrong buffer, a 92/96-byte header mismatch, ABI-name misuse, an unavailable
  rename import, unsafe launcher trust/partial projection, synthetic scheduler
  evidence, and missing SPipe/manual artifacts.
- fix cycle 1: corrected digest comparison and header padding; separated
  `SimpleAppRecordV1` from fixed-width `SimpleAppLaunchV1`; routed config I/O
  through the app facade; changed launcher admission to decode bytes itself,
  prevalidate the complete supported projection, retain app IDs, and fail
  closed on unimplemented policy projection; added scoped system/manual docs.
- open rows: provider query/CLI dispatch, exact unchanged-core artifact proof,
  authoritative artifact-manifest policy projection, real typed-edge
  scheduler/CAS receipts, compiler provider boundary, pure-Simple SPipe
  evidence, and startup/dispatch/RSS measurements remain active.
- highest-capability review 2: REJECT as a complete feature handoff. Earlier
  wire/type/import fixes were accepted, but composition reload retained removed
  apps and the reader admitted non-canonical encodings with recomputed digests.
- fix cycle 2: launcher SCI reload now prevalidates replacement capacity and
  ownership, retires the prior SCI projection, and installs the new projection;
  the reader re-encodes admitted semantics and rejects any non-canonical byte
  representation. No-argument config compiler invocation now exits with usage
  failure instead of success.
- implementation wave 2: added fixed-width provider/CLI descriptors and real
  in-process query/dispatch with native/SMF fail-closed status; upgraded
  build-explain from caller-supplied receipts to a pure typed-edge decision
  engine; projected supported launcher shortcuts and filed
  `doc/08_tracking/bug/sci_launcher_policy_projection_owner_api_missing_2026-08-14.md`
  for capability/association owner APIs that cannot yet preserve SCI policy.
- launcher projection evidence: supported shortcut strings are validated and
  projected through `launcher_register`; malformed shortcuts, scoped
  capabilities, and associations reject before mutation with distinct codes.
  Focused replacement coverage proves renamed and omitted SCI-owned apps are
  removed on the supported success path. Audit found no transactional rollback
  if a future commit-phase owner call fails after retirement; that limitation
  and its owner-level unblock are recorded in the same bug document.
- evidence limitation: wave-2 focused commands also used the deployed Rust
  seed and remain diagnostic despite exit-zero summaries. No result is promoted
  to AC-8 PASS until a genuine pure-Simple binary runs the focused/system gates.
- compiler-provider wave: added the scalar-only `CompilerDriverV1` descriptor
  plus an in-process adapter that owns compiler-private options and results
  behind monotonic numeric session/request/result handles. Focused lifecycle
  and fail-closed query tests exit zero, but were run by the deployed Rust seed
  and therefore remain diagnostic rather than AC-8 evidence.
- compiler-provider blocker: `bootstrap_main.spl:11` remains a concrete driver
  import because no independently built compiler-provider artifact has a
  loader-admitted process-callable query entry. Exact required evidence is in
  `doc/08_tracking/bug/compiler_driver_v1_bootstrap_activation_blocked_on_callable_loader_2026-08-14.md`;
  no fallback or bootstrap was introduced.
- workflow update: the canonical guide permits explicitly admitted Stage 2 or
  Stage 3 Simple binaries for focused pure-Simple compiler/interpreter/loader
  work. Admission requires exact path/hash/stage/provenance/commands, isolated
  output/cache, fail-closed command support, no Rust-seed fallback, and stage-
  scoped evidence that cannot substitute for Stage 4, general SPipe/docgen/test,
  release, convergence/DDC, or cross-host proof.
- highest-capability review 3: REJECT as a complete implementation. The review
  accepted scoped Stage 2/3 policy and conservative Unknown handling, but found
  that named-target execution could accept a stale preexisting output, declared
  dependency artifacts were not consumed by dependent actions, authoritative
  imported-closure/action receipts were absent, and the root target registry
  covered only two proof targets.
- fix cycle 3: named-target actions now build to a freshly removed,
  process-qualified candidate, require a nonempty SHA-256-addressable result,
  and atomically publish only that candidate. Executor reuse remains disabled
  and is reported as such. Dependency-artifact inputs, authoritative closure
  receipts, and the complete product graph remain open in
  `doc/08_tracking/bug/named_target_action_executor_missing_2026-08-14.md`;
  `dev-done` denotes completion of the SPipe dev/refinement phase, not overall
  feature completion.
- build-explain follow-up: typed decisions now carry sorted changed interface
  groups, relevant digest deltas, explicit conservative cache reused/rebuilt
  counts, cache-evidence availability, and rendered `bootstrap-required` plus
  typed reason. This improves receipt completeness without claiming unavailable
  executor/CAS reuse evidence.
- provider-generation follow-up: added an owner-managed activation table that
  validates artifact/callability evidence before mutation, atomically replaces
  the active in-process generation, retains retired generations while pinned,
  and sweeps them only after release. Focused tests passed under the deployed
  seed and therefore remain diagnostic; native/SMF query invocation and loader-
  coupled generation activation remain open.
- highest-capability review 4: REJECT / STATUS FAIL. It confirmed the current
  tree is an incremental proof slice, not the requested end state. Blocking
  rows are the app-only SCI schema/optional-extension canonicalization,
  unchanged static root CLI/core, disconnected dynamic query invocation and
  loader-handle lifetime, incomplete manifest projection/reload rollback,
  concrete compiler-driver bootstrap import, unavailable dependency inputs and
  authoritative action receipts, incomplete product target graph, absent
  admitted pure-Simple/performance evidence, and partial SPipe trace coverage.
  Review positives were the scoped Stage 2/3 policy, direct-env guards, and
  correct `doc/06_spec` layout. Work continues; no verify PASS is claimed.
- post-review refinement: generation pins now have unique owner-issued IDs and
  a live-pin table, so two handles for one generation cannot be released by
  replaying one receipt. This strengthens in-process lifetime safety but does
  not couple a native/SMF library handle to the generation.
- post-review build-explain refinement: the CLI planning surface now emits the
  conservative selected declaration closure, `cache-reused=0`, rebuilt count,
  changed-interface/digest placeholders, unavailable cache/closure evidence,
  and explicit no-bootstrap fields. It still cannot supply authoritative
  compiler digest deltas or reuse receipts.
- SCI provider/CLI section: v1 now canonically encodes interface groups,
  provider artifact identities, bindings, command names/aliases/summaries, and
  capability requirements in a required independently digested section while
  retaining legacy app-only decode. Multi-section composition identity covers
  directory metadata plus payloads; known sections remain canonical even when
  an authenticated unknown optional extension is skipped. Provider paths share
  normalized `build/providers`, `/sys/providers`, and
  `/usr/lib/simple/providers` roots with loader admission. Focused seed-driven
  diagnostics emitted no authoritative results marker and remain non-PASS.
- revised objective: P0 cheap decisions precede core/provider extraction. No
  bootstrap action may start unless the same planner receipt emits a validated
  typed reason. Initial performance regression gates use structural work counts
  (parsed/typed/lowered modules, objects, provider packages, links, SCI sections,
  hits, and misses) rather than host-dependent wall-clock thresholds.
- research/design addendum: CLI-0/1/2, B1/B2/B3, P0/P1/P2/R0, cache layers,
  mutation matrix, config-zero-code acceptance, structural budgets, explain
  receipts, and the normative P0-P8 implementation order are aligned across
  research, requirements, architecture/TLDR, detail design, plans, and guide.
- ad-hoc bootstrap reason gate: the common staged-bootstrap entry now refuses
  missing and `None` receipts before creating output, binds an allowed typed
  receipt to the requested Stage 3 or Stage 4 target, and supports a
  validation-only exit. The focused shell reproduction passed without running
  bootstrap. Ordinary `simple build` cannot auto-select Stage 4. The v1 receipt
  proves canonical planner provenance but is not cryptographic authorization.
- resumed P1/P2 slices: `app.simple_core` now has a fixed CLI-0 resolver and a
  pure router; `app.cli_composition` resolves SCI command names/aliases/help to
  immutable provider activation requests with locked artifact/interface and
  capability identities. These are isolated modules, not yet the deployed
  `bin/simple` composition root. Config-section-only planning records zero
  parsed/typed/lowered modules, objects, and links, with one SCI section.
- provider query/session follow-up: the canonical 44-byte request / 60-byte
  result codec now feeds an exact hosted/native `int32`
  `rt_provider_query_v1_call`; scalar `rt_dyncall_2` remains prohibited.
  Dynamic admission retains its `DynLibKind`, successful query results receive
  unique live pins, replayed release fails, and close refuses pinned sessions.
  Naked evidence remains fail closed. A real provider artifact and admitted
  B2/B3 run are still required before deployed activation is claimed.
- CLI invocation wire follow-up: the public command contract now owns fixed
  28-byte request and 20-byte result headers plus canonical bounded arenas for
  command UTF-8, counted length-prefixed arguments, output, and diagnostics.
  Decoders reject noncanonical offsets, truncation, trailing bytes, invalid
  operations, excessive counts, and absent output capacity. This removes
  language-private strings/arrays from the next dynamic invocation boundary;
  the exact invoke runtime call and real provider execution remain pending.
