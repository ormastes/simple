# Extreme typing and traceability feature expert

Status: design handoff, 2026-11-01; no feature/runtime qualification.

2026-11-02 source candidate: the retained HIR typecheck consumer now projects
owned signature facts from live HM substitutions through
`compiler.types.type_infer.api_signature_projection_v1`, using
`compiler.common.api_signature_facts_v1` records and bounded CompileContext
storage. This adds a `src/compiler/30.types` owner route; it does not establish
effective exports, complete E1, fatal enforcement or engine parity. Archive
leases keep collection absent. Read the [current slice status and
bounds](../../../05_design/extreme_typing_traceability.md#e1-retained-signature-observation-candidate-2026-11-02)
before extending the source. Authored projection/lifetime/storage specs are
unrun pending an admitted runtime; no generated manual or proof is claimed.

2026-11-03 source follow-up adds the HIR frozen export-route projector and
explicit retained-registry driver wiring. It joins physical source/generation
and declaration authority to callable IDs; `Joined` is identity linkage only.
Ancestor/effective external visibility is still Unknown. Read the
[route status](../../../05_design/extreme_typing_traceability.md#e1-frozen-export-route-join-candidate-2026-11-03)
before consuming these records. Tests/performance remain unexecuted.

2026-11-06 adds the pure structural exposure walker
`compiler.types.type_infer.api_exposure_walker_v1` over the retained facts,
returning `compiler.common.api_exposure_result_v1` records (Safe / Violates /
Unknown per callable, export-root-to-leaf paths, fail-closed module verdict).
It classifies only; no named rule, severity, CompileContext retention or
publication guard exists yet. Read the
[walker status](../../../05_design/extreme_typing_traceability.md#e1-structural-exposure-walker-2026-11-06)
before extending it. Its spec and the projection spec executed GREEN on the
Windows seed runner. The route spec was 3/6 until 2026-11-06, when two
production defects were fixed in code: the registry freeze never set
`declaration_authority_index.frozen` (so the authority lookup and the route
projector saw every surface as malformed), and retained facts were keyed by
the filename-derived `HirModule.name` instead of the pass's logical module
key, so registry aliases could not join. Now 7/7 on the seed. Seed GREEN is
unit evidence, not runtime admission; the production join inside a real
`compile()` is pending Phase 3.
The retained typecheck pass also stores the walker result per published
module in `CompileContext.api_exposure`, cleared and replaced with the facts;
a missing row is NotCollected.

2026-11-06 E2: the named rule `extreme_public_api`
(`compiler.common.api_publication_decision_v1`) and the driver guard
(`compiler.driver.driver_api_publication_guard_v1`) deny a joined violating
export root at robust/critical/verified, warn at strict, advise at moderate,
at one phase-5 choke point before interpret/JIT/AOT. Activation is explicit
(`SIMPLE_EXTREME_PUBLIC_API=1`) until the stdlib is migrated; Unknown denial
is deferred to E1 export closure. Read the
[E2 status](../../../05_design/extreme_typing_traceability.md#e2-named-rule-and-publication-guard-2026-11-06)
before extending; the full `compile()` denial is pending a self-hosted run.


2026-11-06 E1 closure design: the
[effective export closure](../../../05_design/extreme_typing_traceability.md#e1-effective-export-closure-design-2026-11-06)
is defined over the frozen registry, route facts and retained signatures:
`Exported` needs a `Joined` direct route plus a `Joined` route from every
ancestor facade present in the registry (`export use` only; `pub mod` is not
parsed by the compiler frontend; a bare `pub fn` without `export` is
`NotExported`). Closure is relative to the compilation subject and follows
`visibility.spl`, not `visibility_checker.spl` (which treats `Public` as
everywhere). After the closure is applied a module can be `Safe`; `NotExported`
callables never drive the verdict; Unknown denial may then activate under the
explicit flag, which denies every `Nominal` export until members are projected.
Design only; the code slice follows as its own PR.


2026-11-06 E1 closure implemented: `compiler.hir.hir_lowering.api_export_closure_projection_v1`
projects `CompileContext.api_export_closure_facts`;
`compiler.types.type_infer.api_exposure_closure_v1` applies it so a module
verdict can be `Safe` (callable surface only; the unconditional scope marker
`non-callable-and-generated-surfaces-not-collected` stays listed and does not
block). A facade that spells an export the builder could not resolve is
`Unknown(export-origin-unresolved:...)`. The decision excludes `NotExported`
roots and now denies Unknown roots at a denying profile under the explicit
flag. See the
[implemented note](../../../05_design/extreme_typing_traceability.md#implemented-2026-11-06-follow-up-to-the-design-above).

Read the [selected policy](../../../02_requirements/feature/extreme_typing_traceability.md),
[architecture](../../../04_architecture/extreme_typing_traceability.md),
[implementation plan](../../../03_plan/agent_tasks/extreme_typing_traceability.md)
and [acceptance plan](../../../03_plan/sys_test/extreme_typing_traceability.md).
The existing [traceability roadmap](../../../09_report/simple_traceability_sdn_slop_final_2026-10-03.md)
retains its selected 20 requirements and 40 criteria.

Robust+ public Simple APIs may expose no bare true builtin primitives, including
bool/text/char; public generics require domain-safe bounds. Easy nominal
construction is required. Private representation is legal; public raw
constructors/getters/conversions, allowlists and private-FFI reexports cannot
bypass the rule. Compiler owns canonical types/effective visibility.

Extend common traceability and existing Slop; one projection supplies all
adapters. Caret owns session/worktree lifecycle. Keep definitions, observations
and qualified evidence distinct. Read-only overlap is not a merge conflict.
Open architecture options do not reopen the selected language policy.

Consume the exact feature/layer receipt before source work. New source routes,
manuals and implementation claims require revalidation; this expert note does
not activate proposed CLI commands or broaden operational skills.
