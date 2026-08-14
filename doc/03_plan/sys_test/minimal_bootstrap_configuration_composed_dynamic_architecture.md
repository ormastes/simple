<!-- codex-design -->

# System Test Plan: Minimal-Bootstrap Configuration-Composed Dynamic Architecture

## Executable and manual locations

- Executable: `test/03_system/app/simple/feature/minimal_bootstrap_configuration_composed_dynamic_architecture_spec.spl`
- Mirrored manual: `doc/06_spec/03_system/app/simple/feature/minimal_bootstrap_configuration_composed_dynamic_architecture_spec.md`
- Evidence: `build/test-artifacts/03_system/app/simple/feature/minimal_bootstrap_configuration_composed_dynamic_architecture/`

The spec uses built-in matchers only. The manual shows primary operator flows; setup is hidden with `@inline`/`@prev`, matrices are folded, and executable SPipe is folded by default.

## Shared scenario vocabulary

- visible flow steps: `step("compile_composition")`, `step("load_unchanged_core")`, `step("dispatch_provider")`, `step("explain_rebuild")`
- setup: `setup_minimal_bootstrap_fixture`
- checkers: `check_composition_image`, `check_rebuild_receipt`, `check_bootstrap_reason`
- incomplete helper rule: call `assert(false)` or `fail(...)`

## Scenarios and traceability

| Scenario | Requirements | Observable evidence |
|---|---|---|
| Compile equivalent reordered sources | REQ-001; NFR-001 | identical bytes/digest; read-back identity |
| Reject malformed images; skip optional extension | REQ-002; NFR-002, NFR-011 | stable rejection codes for bounds, overlap, hash, binding, slot, path, interface; optional skip |
| Project app policy through one manifest | REQ-003; NFR-003 | SCI and `SimpleArtifactManifest` agree; conflicting legacy record rejected |
| Change app record through unchanged core | REQ-004, REQ-008; NFR-004, NFR-008 | same core digest, new catalog value, zero compile/bootstrap actions |
| Query compatible and incompatible providers | REQ-005, REQ-006, REQ-014; NFR-011 | old/new minor success; major/short/duplicate/unstable failure |
| Dispatch leaf CLI provider | REQ-007; NFR-006, NFR-008 | command result plus provider-only/SCI closure |
| Missing provider fails without compilation | REQ-009; NFR-003, NFR-010 | `ProviderArtifactMissing`; no process/build action |
| Body-only edge turns green | REQ-010; NFR-009 | implementation delta, stable interface/ABI/semantic identities, zero dependents |
| Explain rebuild closure | REQ-011; NFR-010 | all receipt fields and counts present |
| Unknown compatibility rebuilds | REQ-011, REQ-014; NFR-011 | no reuse decision; smallest producer selected |
| Full bootstrap requires typed reason | REQ-012; NFR-010 | empty/disallowed reason rejected; allowed incompatibility accepted |
| Trust targets remain explicit | REQ-013; NFR-008 | convergence/DDC absent from feature closure, present when requested |
| Pin provider generation during replacement | REQ-015; NFR-002 | old handle remains valid; failed query preserves active generation |
| Compiler boundary rejects internal layout | REQ-016 | opaque handle descriptor; no AST/HIR/MIR/native object fields |
| Cache namespace evolution | REQ-017; NFR-009 | new namespace, old artifacts retained, no global-clear action |
| Guidance audit | REQ-018; NFR-012 | every required surface changed or recorded N/A; manual has no placeholder pass |
| Startup/help structural work | NFR-004, NFR-005, NFR-006, NFR-007 | CLI-0 trace; parsed/typed/lowered, objects, providers, links all zero; SCI/cache counters; timing/RSS host-labeled observations |

## Primary operator flow

1. Setup a minimal app and leaf-command fixture silently.
2. `compile_composition`: compile and validate the baseline SCI.
3. `load_unchanged_core`: record core identity, edit app metadata, rebuild SCI, and load the same core.
4. `dispatch_provider`: edit a private provider behavior, rebuild and dispatch through the unchanged registry/core.
5. `explain_rebuild`: inspect containment, digest deltas, reuse counts, and bootstrap decision.

The generated manual must explain this flow without exposing setup implementation. Binary receipts and timing data use typed `binary`, `artifact`, `exec`, or `log` capture metadata.

## Focused matrix checks

Composition: deterministic ordering; unknown required/optional sections; truncated directory; checked overflow; overlapping sections; hash/signature mismatch; duplicate binding; undeclared slot; unsafe path; missing required/optional provider.

Provider: compatible minor prefixes; unsupported major; descriptor shorter than required; duplicate interface ID; interface set changes between queries; query crash/status failure; non-callable SMF evidence; unload while pinned.

Invalidation: body/private/public signature/ABI ownership/macro-CTFE-AOP/tool behavior/config projection changes. Every mutation asserts the exact rebuilt and reused sets.

Bootstrap: app and leaf CLI mutations invoke zero bootstrap targets; compiler-private mutation leaves core unchanged; backend mutation leaves frontend unchanged; full bootstrap always has an allowed reason.

The harness classifies CLI-0/1/2 and identifies B1/B2/B3 producer plus
P0/P1/P2/R0 product. It rejects bootstrap whose typed reason was not emitted
before execution. Config-zero-code asserts every code-work counter is zero and
only declared SCI sections regenerate.

Scenario growth follows P0–P8: cheap-decision/reason guards first, then core,
CLI configuration, essential provider, leaf providers, per-module cache,
compiler engine provider, full product composition, and release-bootstrap
scenarios. R0/convergence/DDC scenarios remain explicit release evidence.

## Verification commands and guardrails

Run each focused passing criterion once per session. Use at most three fix/verify cycles. Generate the manual with the canonical SPipe doc generator, run `sspec-maintain scan`, and require zero stubs. Before acceptance, `find doc/06_spec -name '*_spec.spl'` must return no paths. Runtime commands normally use deployed Stage 4. Focused pure-Simple compiler/interpreter/loader criteria may use an explicitly admitted Stage 2/3 binary under the canonical guide, with stage-scoped evidence; never silently use the Rust seed.
