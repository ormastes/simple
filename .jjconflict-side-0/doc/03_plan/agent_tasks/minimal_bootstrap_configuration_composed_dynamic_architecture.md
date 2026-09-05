<!-- codex-design -->

# Parallel Agent Plan: Minimal-Bootstrap Configuration-Composed Dynamic Architecture

## Governance

- Merge owner: root Codex agent.
- Final reviewer: a fresh highest-capability agent after all lanes integrate.
- Final review covers requirements traceability, architecture coherence, exclusions, rebuild evidence, generated-manual quality, documentation consistency, dirty-work ownership, and PASS evidence.
- Agents edit only declared ownership. Existing unrelated dirty files belong to other sessions.
- Shared contracts and scenario vocabulary below are frozen before sidecars start.

## Frozen names

- Interfaces: `SimpleCompositionImageV1`, `SimpleProviderQueryV1`, `SimpleCliCommandV1`, `SimpleAppLaunchV1`.
- Manual flows: `compile_composition`, `load_unchanged_core`, `dispatch_provider`, `explain_rebuild`.
- Helpers: `setup_minimal_bootstrap_fixture`, `check_composition_image`, `check_rebuild_receipt`, `check_bootstrap_reason`.
- Incomplete helper policy: `assert(false)` or `fail(...)`; never placeholder success.

## Lanes

| Lane | Capability/reviewer | Ownership | Deliverable and gate |
|---|---|---|---|
| L0 contracts/prerequisites | highest-capability primary; lower-model sidecar N/A because wire/ABI decisions require authoritative review | SMF wire spec/tests, target IR integration, ownership inventory | cross-reader evidence; tracked typed target base; no overwrite of concurrent work |
| L1 composition | normal/high agent; optional Codex Spark read-only inventory sidecar | composition schema/common codec, `simple-configc`, focused unit/integration tests | deterministic output and complete malformed-input matrix |
| L2 app proof | normal/high agent; optional Claude Haiku read-only catalog inventory | launcher/app/association compatibility adapter and fixture | app edit changes SCI only; one-manifest projection proved |
| L3 provider/CLI proof | normal/high agent; optional Codex Spark leaf-tool dependency survey | provider ABI/loader generation slice, CLI registry/provider, focused tests | private edit rebuild containment and fail-closed activation |
| L4 scheduler/bootstrap | highest-capability primary; lower-model sidecar may inventory digest call sites only | typed edges, compatibility, receipt/CAS, reasons/named targets | exact rebuild sets; unknown never reused; trust targets explicit |
| L5 SPipe/manual | normal/high agent; lower-model sidecar may draft folded matrix descriptions | executable system spec and generated manual | real assertions, shared helpers, zero stubs, readable primary flow |
| L6 guidance/wiki/process | normal/high agent; Claude Haiku or Sonnet inventory sidecar | skills, SPipe docs, LLM wiki/process, developer guides, tracking gaps | every requested surface updated or N/A with concrete reason |
| L6a compiler driver provider | highest-capability implementation/review | `src/compiler/80.driver/driver_provider_*_v1.spl`, focused provider tests; bootstrap entry only after callable admission | opaque session/request/result handles; no IR exposure; dynamic modes fail closed; exact bootstrap-import blocker if loader unavailable |
| L7 integration verification | root merge owner | conflict resolution and focused checks | no unrelated work absorbed; per-criterion once-only evidence |
| L8 final review | fresh highest-capability reviewer | read-only whole-scope audit, then root fixes | explicit accept/reject against all requirements and exclusions |

## Dependency waves

Normative product vocabulary: CLI-0 static recovery core; CLI-1 essential
provider; CLI-2 extended providers. B1 is the Rust seed, B2 the pure-Simple
bootstrap compiler, and B3 the admitted self-host compiler. P0 is simple-core,
P1 essential CLI, P2 optional providers, and R0 the release bundle. No bootstrap
task starts before an allowed typed reason is emitted.

Implementation phases: P0 cheap decisions; P1 core extraction; P2 CLI
configuration; P3 essential provider; P4 leaf providers; P5 per-module cache;
P6 compiler engine provider; P7 full product composition; P8 release bootstrap.

1. L0 freezes SCI header/directory, provider query ABI, interface ID encoding, target labels, canonical digest encoder, and one-manifest ownership.
2. L1 implements codec/compiler/readers. L2 may prepare adapters but cannot finalize until L1 views stabilize.
3. L2 and L3 build independent proof slices against frozen contracts.
4. L4 makes their identities authoritative scheduler inputs.
5. L5 integrates executable evidence after helper APIs exist; L6 can proceed concurrently from frozen policy.
6. L7 merges and verifies once; L8 performs the independent high-capability audit.

## Per-lane work-order fields

Every dispatched task declares `target`, `owns`, `forbidden`,
`interface_groups_changed`, `expected_rebuild`, B1/B2/B3 producer,
P0/P1/P2/R0 product, structural counter budgets, and `bootstrap_reason`.
Default forbidden scope includes release/tag/push, unrelated dirty files,
vendored runtime sources, and other lanes' owned directories.

Example leaf lane:

```yaml
task:
  target: //compiler:formatter_provider
  owns: [src/compiler/90.tools/formatter/**]
  forbidden: [scripts/bootstrap/**, src/spec/composition/**]
  interface_groups_changed: []
  expected_rebuild: [//compiler:formatter_provider, //config:default_sci]
  bootstrap_reason: none
```

## Documentation surface audit

L6 must inventory `.codex/skills/`, `.agents/skills/`, `.claude/skills/`, `.claude/agents/spipe/`, `.claude/commands/`, `.gemini/commands/`, `doc/07_guide/`, relevant SPipe documents, and `doc/00_llm_process/`. A surface is `N/A` only when it has no feature-development/bootstrap instruction; record the inspected path and reason. Create feature-expert and appropriate build/compiler layer-expert knowledge. Any known unfixed gap receives a bug record with file/line, impact, owner/unblock condition, and evidence.

## Integration gates

- Selected requirements and design remain traceable to executable scenarios.
- No second launch/application authority is introduced.
- No startup compilation, Rust-seed fallback, cache-wide deletion, or compiler-internal stable ABI exists.
- App/CLI proof receipts show exact containment.
- Convergence and DDC remain explicit release/trust targets.
- Generated manual is operator-readable and no `.spl` lives under `doc/06_spec`.
- Higher-capability review accepts both implementation and exclusions before verify can report PASS.
