# Research: Aerospace-Grade Hardening for Simple — reuse `critical`, add `flight-core-v1` + `aero-a`/`space-a`

**Date:** 2026-08-07
**Status:** research — external precedent is *as-cited, unverified*; repo-state claims
are individually verified with `file:line` (see § Measured repo state).
**Companion:** [`resource_unified_ownership_research_2026-08-06.md`](../resource/resource_unified_ownership_research_2026-08-06.md)
(the `resource` ownership campaign; its allocation/move work is the substrate this
document's allocation-class analysis builds on).

---

## 1. The decision, restated

A separate `space_critical` **language strictness profile is rejected**. The canonical
profile is already `critical` (`mission-critical` / `mission_critical` are deprecated
aliases — `doc/02_requirements/language/mission_critical_profile.md:146-156`). Simple
already treats strictness and runtime family as orthogonal axes.

The composition is four independent concerns:

| Axis | Existing Simple mechanism | Owns |
|---|---|---|
| Language strictness | `critical` | types, contracts, effects, unsafe boundaries, fail-closed compiler behaviour |
| Runtime semantics | `nogc_*` / `gc_*` / `*_noalloc` families | allocation, GC, synchronization, scheduler, platform APIs |
| Assurance grade | `aero-a` / `space-a` | proof, MC/DC, tool qualification, traceability, reproducibility, release evidence |
| Mission deployment | SDN configuration | CPU, board, task periods, fault policy, partitions, memory map, external assumptions |

User-facing, the project writes only:

```
assurance:
  preset: space-a
```

which the resolver expands to `strictness: critical` + convention `flight-core-v1` +
zero-unwaived-warning policy + qualified static/bounded runtime + required whole-program
closure + required binary assurance seal + `space-a` evidence policy.

`flight-core-v1` is a **coding convention set**, not a fifth strictness tier.
`aero-a` and `space-a` differ only in evidence mapping (airborne vs. space standards),
not in source rules.

---

## 2. External precedent (as-cited, unverified)

These citations come from the originating proposal and are recorded verbatim as design
rationale. They were **not** re-verified against the published standards in this session
(network fetch is blocked in this environment, and a wrong revision date does not change
the plan the way a wrong repo fact does). Anyone converting these into certification
evidence must re-verify against the controlled documents first. See also [`doc/04_architecture/language/assurance/standards_crosswalk_2026-08-07.md`](../../../04_architecture/language/assurance/standards_crosswalk_2026-08-07.md) for the mapping of Simple's `FLT-*` rules to these external standards (WP-1).

| Source | Cited claim | Why it matters here |
|---|---|---|
| ECSS-E-ST-40C Rev.1, 2025-04-30 | full engineering lifecycle, explicit project tailoring | space missions do **not** imply a new language dialect |
| ECSS-Q-ST-80C Rev.2, 2025-04-30 | software product assurance, tailorable | assurance grade is a project axis, not a syntax axis |
| NASA-STD-8739.8B / NASA handbook | no single mandated C/C++ standard; each project selects, tailors, adheres, verifies; safety-critical classification derives from **hazard analysis** | mixed-criticality classification cannot be inferred from source — it is one of the few legitimate configuration inputs |
| JPL *Power of Ten* | simple control flow, bounded loops, no allocation after init, short functions, meaningful assertions, minimal data scope, checked returns, restricted preprocessor/pointers, pedantic zero-warning | the source-code core of `flight-core-v1` |
| JSF AV C++ | rule strength tiers + formal exception process; cyclomatic ≤ 20; ≤ 200 logical SLOC/function; 206 of 233 rules statically enforceable | justifies a **rule-level** ladder rather than one uniform severity |
| CERT | *rule* (likely defect, determinable conformance) vs. *recommendation* (quality) | same distinction, adopted below as `Shall` vs. `Should` |
| SPARK (Silver level) | absence of runtime errors + initialization, data-flow, global-access, termination | the AoRTE obligation set Simple should generate |
| Ravenscar | restricts an *existing* tasking model: static tasks, restricted queues, no dynamic priorities, no task allocators, analyzable locking | the exact architectural precedent for "concurrency subset of `critical`", not a new task grammar |
| F´ (NASA) | components, typed ports, topologies, deployments; commands/telemetry/events as *framework* concepts | validates reusing MDSOC capsules + `__init__.spl` exports instead of a `component` keyword |
| seL4 capDL | declarative capability distribution defines access-control boundaries | model for a generated capability topology manifest |
| CompCert | proven semantic preservation source → assembly | the long-term backend target; translation validation first |
| TACLeBench | WCET benchmark corpus | independent validation of a WCET analyzer, decoupled from project code |
| ARCHIE | transient/permanent fault injection into instructions, RAM, flash, registers | fault-campaign adapter target |
| cFS/RISC-V fault study (2025) | faults often manifested as **unresponsiveness**, not wrong return values | campaigns must test liveness and recovery, not only output equality |
| RTEMS space qualification | broad API + a *qualified subset* + target-specific testing | model for a qualified-dependency manifest instead of a duplicate `std.critical` |

**Key inference:** every one of these separates *language rules* from *runtime restriction*
from *proof level* from *release evidence*. None of them creates a per-domain dialect.

---

## 3. Design rules adopted

1. **No new grammar by default.** A construct is rejected unless the property cannot be
   expressed with current contracts/types/effects/modules/traits **and** cannot be
   reliably inferred from HIR/MIR.
2. **Convention discovers; semantic structures prove.** `health.spl` is *discoverable* by
   name; it is a *valid* health provider only when it implements the interface and passes
   the checks. Correctness rests on exported module boundaries, types, trait impls,
   contracts, effects, SymbolIds, MIR and object-code facts.
3. **Infer first; configure only external facts.** Infer call closure, capabilities,
   effects, allocation, loop bounds, stack frames, bounded capacity, panic/trap paths,
   dynamic-dispatch targets, test/proof links. Configure only what source cannot know:
   processor and memory timing, task period/deadline, core assignment, partition mapping,
   watchdog properties, radiation policy, trusted external library behaviour, approved
   deviations.
4. **`critical` is transitive.** Marking the top-level file is insufficient; every symbol
   reachable from a critical root is analyzed under the critical contract.
5. **Heavy evidence belongs to the release gate**, not to a second profile. MC/DC, HIL,
   proof regeneration, WCET and reproducible builds are progressively heavier gates over
   the *same* `critical` source.
6. **Unknown means blocked.** An unresolved call target, unknown allocator behaviour,
   unavailable proof tool, stale evidence or unsupported backend lowering must never
   silently become a pass.

### Rule-strength ladder (from JSF + CERT)

| Class | Meaning | `critical` dev | `aero-a` / `space-a` release |
|---|---|---|---|
| Intrinsic | impossible in the language, or eliminated during lowering | always satisfied | always satisfied |
| Shall | violation can introduce a correctness/safety defect | error | error |
| Will | required convention or analyzability constraint | warning during migration | error unless approved deviation |
| Should | maintainability / review recommendation | warning + metric | reviewed warning, or project-tailored error |
| Evidence | not establishable from source alone | report | release blocker |

Release presets apply a zero-warning policy: unwaived compiler warnings `0`, unwaived
static-analysis findings `0`, unknown analysis results `0`. A "harmless" warning is closed
by a reviewed deviation or by rewriting the code — never by silent suppression.

---

## 4. Reuse the existing grammar

Simple already carries the required surface. The right-hand column is what this research
**rejects adding**.

| Property | Existing mechanism | Do not introduce |
|---|---|---|
| Preconditions | `in:` | a `requires` replacement |
| Postconditions | `out(ret):`, `out_err(err):` | `ensures` |
| Invariants | `invariant:` | invariant decorators |
| Termination | `decreases:` | `@terminates` |
| Proof association | `proof uses:` | a new proof annotation family |
| Value constraints | `type T = Base where ...` | range-type grammar |
| Domain separation | newunits, enums, `Option`/`Result` | space-only primitives |
| Effects | `@pure`, `@io`, `@net`, `@fs`, `@unsafe`, `@async` | a second effect system |
| Capabilities | `requires [...]` | new capability grammar |
| Module boundary | `__init__.spl`, `pub mod`, `export use` | a `component` keyword |
| Architectural capsule | MDSOC capsule/module model | a `partition` keyword |
| Allocation prohibition | `@noalloc` + runtime manifest | `no_heap` / `no_gc` / `bounded_alloc` |
| State-transition safety | `enum` + exhaustive `match` + `invariant` | a `state_machine` keyword |
| Timing budget | deployment SDN + WCET result | `@wcet(100us)` |
| Static task mapping | scheduler/deployment config | `task period ...` grammar |

**Revision to the planned REQ-MC-004 unsafe-boundary design.** The parameterized form
`@unsafe(reason: ..., capabilities: [...])` is unnecessary. Keep the existing `unsafe:` /
`@unsafe` marker as the source boundary, and hold reason/capabilities/owner/reviewer/
evidence in a central **SymbolId-keyed review manifest**. This keeps the grammar unchanged
and makes review data auditable independently of source comments.

---

## 5. What Simple can enforce that a C checker cannot

Simple owns parser, type system, HIR, MIR, linker, loader, runtime families, tests, proofs
and artifact format. The *Power of Ten* rules therefore map onto **semantic** checks, not
textual ones — that is the central technical opportunity.

| Flight rule | Simple enforcement | Severity |
|---|---|---|
| No `goto`/`setjmp`/`longjmp` | not in the grammar | Intrinsic |
| No uncontrolled recursion | call-graph SCCs; reject direct+indirect recursion in `flight-core-v1`; plain `critical` permits it only with a proved finite `decreases:` | Shall |
| Bounded loops | infer from ranges, fixed collections, refinement types, constants; else require `invariant:`/`decreases:` or an external target constraint | Shall (error if unknown) |
| No allocation after init | classify `none` / `init_only` / `bounded_pool` / `unbounded` / `unknown`; seal runtime topology after startup | Shall (error on unbounded/unknown) |
| Bounded stack | final object frame + max call chain + interrupt nesting + coroutine state | link error if unknown |
| Small functions | count **semantic statements, nesting, exits, cyclomatic complexity** — never physical source lines | Should → Will |
| Minimum data scope | HIR use-range analysis; module mutable globals need an approved owner + sync model | Will → Shall |
| No unencapsulated global state | MDSOC capsule owner + read/write-set analysis | Shall |
| All values initialized | definite-initialization, path-sensitive | Shall |
| No dummy value hiding a missed assignment | detect write-before-read where a default initializer only suppresses uninitialized analysis | Will → Shall |
| Checked returns | `Result`/status/resource-handle/must-use cannot be silently discarded | Shall |
| Validated inputs | refinement types, `in:`, domain types, explicit decoder validation | Shall at external boundaries |
| Safe arithmetic | prove or check overflow, div-by-zero, invalid shift, narrowing | Shall if neither proved nor checked |
| Array bounds | HIR/MIR range proof or retained bounds check | Shall if unclassified |
| Float determinism | no fast-math in flight closure; explicit NaN/Inf, rounding, contraction policy | Shall |
| Representation assumptions | explicit layout, generated serializers, static size/offset assertions | Shall |

Language-abstraction rules — the concerns a C standard states as pointer/preprocessor
restrictions become closure questions in Simple:

| C/C++ concern | Simple equivalent | Enforcement |
|---|---|---|
| Preprocessor complexity | macros, compile-time AOP, conditional variants | expand before assurance analysis; retain + hash the expansion; reject unresolved conditional variants |
| Function pointers | callbacks, trait dispatch, events, DI, AOP advice | closed target set required in the critical closure |
| Raw pointers | SFFI, MMIO, backend primitives | only inside a reviewed unsafe/representation boundary |
| Exceptions | panic, unchecked trap, uncaught runtime error | no escape from the critical closure; typed `Result`/enum recovery |
| Deep inheritance | class/trait hierarchy | depth limit; method resolution must be unambiguous |
| Dynamic binding | trait dispatch, loader, plugin/AOP weaving | closed-world during a flight build; no unbounded runtime weaving |
| Unsafe casts | representation conversion, FFI layout | explicit boundary + size/alignment/range validation |
| Unqualified libraries | any stdlib/native/SFFI provider | per-symbol qualified-dependency manifest |
| Conditional-compilation explosion | target selection, feature config | enumerate supported configurations; prove/test each release configuration |

### Assertions: reject the density metric as a gate

*Power of Ten* recommends ~2 assertions per function, but a count-based gate manufactures
meaningless assertions. Simple should count **all** of these as defensive evidence:
refinement-type proof, `in:`, `out:`, `invariant:`, checked `Result` handling, range/bounds
proof, meaningful runtime assertion, formal theorem.

The hard requirements instead are: every external/interrupt/message/storage/FFI boundary
has a validity contract; assertions are side-effect free; tautological and contradictory
assertions are **errors**; every failure has a defined recovery or propagation action; and
tests or proofs demonstrate that the meaningful checks can actually fail on invalid input.
Density stays a project metric, never an override on a function already proved by types.

---

## 6. Catching incomplete implementations (provenance-neutral)

Do **not** attempt to detect LLM-authored code — unreliable and unnecessary. Apply checks
that make the characteristic failure modes impossible to hide:

- **Whole-project symbol resolution before lowering** — two passes (collect declarations →
  resolve every identifier). In `critical`: unresolved name, ambiguous name, undeclared
  cross-file use, unresolved weak symbol and unknown runtime intrinsic are all errors. The
  lenient fallback may survive for bootstrap, but must be prohibited in the critical closure.
- **Extern/native provider closure** — every `extern fn` resolves to exactly one provider
  class. Declared-with-no-provider, signature mismatch, multiple incompatible providers,
  unqualified provider, test mock reaching a flight build, unavailable intrinsic, and
  weak zero/default providers that would hide failure are all gated.
- **Implementation-completeness obligations** for trait methods, abstract methods, exported
  interfaces, DI providers, AOP advice targets, event/interrupt handlers, callbacks,
  state-machine transitions, serialize/deserialize pairs, driver ops, loader hooks, backend
  instruction handlers. Each must be implemented exactly once, explicitly abstract outside
  the closure, or covered by an approved external provider.
- **Strong placeholder checks** — in a critical closure these are errors absent a reviewed
  deviation: `pass_todo`, `pass_dn`, `pass_do_nothing`, bare `pass` in a concrete function,
  empty concrete body, `todo(...)`, panic as normal control flow, `unreachable` fabricating
  exhaustiveness, constant default return with unused inputs, `Ok(nil)`/`false` as fabricated
  success, a `_noop_` name without a NoOp contract, and a comment claiming "implemented" with
  no semantic body. **A name is never sufficient** — intentional no-ops implement a typed
  interface with contracts.
- **Requirement/evidence links as a validated graph**, not strings: requirement → design →
  SymbolId → implementation → test example → proof obligation → MIR function → object symbol
  → binary. Validate existence, resolution, actual execution, checked theorems, present
  object symbols, matching evidence hashes; reject stale line-number-only links, orphan
  requirements, and implementations with no upstream requirement.
- **Test-vacuity and mutation checks** — detect tautological assertions, assertion-free
  tests, print-only tests, always-success matchers, tests that never call the target
  SymbolId, tests swallowing all errors, always-true/always-false contracts, and tests whose
  result is independent of the implementation. For critical requirements, run focused
  mutation checks (default return, negated branch, removed error propagation, skipped state
  update, moved comparison boundary, deleted enum arm); at least one linked test or proof
  must reject each applicable mutant. This is a far stronger completeness signal than
  coverage percentage.

This section is the highest-leverage part of the whole proposal for Simple's *current*
situation: the repo's own measurement history (see MEMORY index, "Measurement traps")
records repeated false-green results from vacuous specs, fail-open guards, and shim
duplication. Vacuity detection and mutation checks attack that class directly.

---

## 7. Enum and skip design (the two named semantic gaps)

**Enums.** Every ordinary Simple enum is **closed by default**; no annotation needed. In
`critical`: all variants listed; wildcard on a closed enum is an error; bare lowercase
binder arms are errors; duplicate/unreachable arms are errors; missing payload patterns are
errors. Only wire/FFI/storage enums need the exception, via the already-planned attribute
mechanism (`@evolving`) with an explicit `Unknown(raw)` arm — never `_`.

The implementation must be **type-resolved**: a canonical HIR `ResolvedMatchCoverage`
record keyed by `scrutinee_type_id` + `enum_symbol_id` + declared/covered variant **ids**,
never by variant spelling or a global bare-name table. MIR lowering refuses to lower an
unapproved incomplete critical match, which is what makes interpreter, MIR interpreter,
JIT, Cranelift, LLVM, native and SMF loader agree. The runtime fall-through guard stays as
defence against corrupted discriminants, malformed FFI data, radiation-induced corruption
and toolchain faults.

Diagnostics: `E-FLT-ENUM-001` omitted variants · `-002` wildcard on closed enum · `-003`
duplicate/unreachable arm · `-004` `@evolving` without explicit `Unknown` · `-005` invalid
discriminant crossing a representation boundary.

**Skips.** No new grammar. Normal profiles keep free-text `skip(...)`. `critical` requires
a resolvable record — `skip("...", skip_ref("SKIP-HW-0042"))` — resolving into existing SDN
tracking data carrying category, reason, owner, requirement, alternative evidence, required
venue, expiry and issue. In `critical`, these are errors: `skip_it`, bare `pending(name)`,
free-text-only skip, empty/weak reason, missing issue/waiver record, unknown requirement,
expired skip, missing owner, missing required venue.

A skipped test **blocks** `aero-a`/`space-a` release when it is the only evidence for a
critical requirement, its waiver expired, its issue/requirement does not resolve, the
alternative test did not run, the required venue (QEMU/HIL/physical) was absent, the skip
count rose above the approved baseline, or it hides a tool failure instead of reporting a
blocked gate. Release reports distinguish: not applicable · environment unavailable · known
defect · temporary waiver · alternative venue covered · release blocker.

---

## 8. Deterministic concurrency, deployment, FDIR, binary seal

**Concurrency = a Ravenscar-style subset of `critical` over existing APIs**, not new task
grammar: task set created only during initialization; no creation after seal; no dynamic
priorities; no unbounded worker pool; no silent inline fallback where parallelism is
required; no termination outside the declared lifecycle; no suspension holding an ordinary
lock; fixed queue/channel capacities; priority-ceiling locking; bounded blocking; static
interrupt binding; explicit CPU assignment on multicore.

**Timing lives in deployment SDN**, not annotations — the same code runs on different
processors at different rates. Task entry SymbolId + `period_us` / `deadline_us` /
`budget_us` / `priority` / `core`. WCET pipeline: contracts + inferred bounds → HIR/MIR CFG
→ optimized object code → target processor/memory model → safe bound → response-time
analysis → compare with the configured budget. Start single-core, deterministic
cache/scratchpad, cyclic-executive or fixed-priority, static interrupts. **No multicore
hard-real-time claim** until cache, bus, memory-controller and interrupt interference are
modeled.

**Architecture reuses MDSOC + `__init__.spl`** — a directory boundary already gives private
implementation, explicit exports, inherited attributes, architectural visibility and a
natural capsule. Capsule boundary = **logical** fault domain; deployment config maps logical
domains onto SimpleOS processes, address spaces, MPU/MMU regions, time partitions, cores,
restart domains and DMA/interrupt capabilities. Capability topology is **generated** from
imports + `requires [...]` + effects + exports + driver bindings + DI topology + IPC.

**FDIR extends existing infrastructure** (timeout detection, recursion-depth detection,
execution-count limits, watchdog facade, chaos/fuzz modes, replay/checkpoint, SimpleOS
release gates) with ordinary library families — `health`, `deadline`, `freshness`, `limit`,
`safe_state`, `command_sequence`, `restart`, `protected_state`, `checkpoint`, `journal`,
`voting`, `fault_event`, `fault_injection` — as plain classes/traits, no new syntax.
Watchdog hierarchy: hardware → kernel/partition → component heartbeat → task deadline →
operation timeout.

**Radiation/state integrity:** library types (`Timestamped<T>`, `Validated<T>`,
`ProtectedState<T>`, `CrcState<T>`, `ReplicatedState<T>`, `Checkpointed<T>`,
`MonotonicSequence<T>`), persistent writes as write-inactive → checksum → read-back →
atomic generation switch. Compiler-assisted duplication/TMR is an **optional pass selected
by deployment policy and validated by fault injection** — never automatic for all critical
code, never assumed to guarantee independence.

**Binary seal:** extend the existing unified artifact manifest (do not create a second
one) with `assurance` / `results` / `evidence` sections plus a small per-object
`AssuranceObjectNoteV1` as transport metadata. The critical linker rejects mixed
critical/non-critical objects, rule-set/target/runtime mismatches, missing notes,
unresolved or weakly-fabricated symbols, unbacked externs, missing implementation
obligations, incomplete enum coverage, forbidden allocator symbols in the steady-state
closure, warnings in a release build, stale dependency hashes and unapproved deviations.
The SimpleOS loader enforces `loader.minimum_assurance`; a flight loader must never
"warn and continue" on a failed required policy.

**Deviations** are centrally recorded per rule-id + SymbolId with reason, hazard,
mitigation, evidence, owner, reviewer and expiry. The compiler verifies the rule exists,
the SymbolId exists, the **source hash still matches the reviewed version**, the scope is
that symbol only, hazard/mitigation/review are present, and the expiry has not passed. The
release binary carries the deviation-manifest hash. A bare local `@allow(rule)` with no
reviewed record is not permitted in a flight build.

---

## 9. Single generated rule registry

One canonical registry in the low-dependency layer
(`src/compiler/00.common/assurance/flight_rules.spl`) holds `FlightRule { id, title,
sources, category, enforcement_phase, critical_level, aero_a_level, space_a_level,
analyzer, deviation_policy, diagnostic, fix }`. From it, **generate** lint severity tables,
compiler diagnostics, the human coding guide, the standards cross-reference, the deviation
template, the binary rule-set hash, IDE/LSP explanations and release-gate requirements.

This exists specifically to prevent the drift this repo has already demonstrated, where a
rule appears in requirements, configuration and documentation but is never actually invoked.

---

## 10. Measured repo state

See § "Verified premises" in the plan document
[`doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`](../../../03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md),
which carries the `file:line` verdict for every repo claim this research depends on, plus
the per-workstream **reachability** column (which binary enforces a check, and whether that
binary reaches users today).

The single dominating constraint, already established by the `resource` campaign: `bin/simple`
is the Rust seed and stage-3 self-host is blocked, so a check added under `src/compiler/**`
produces **zero user-facing enforcement** until that lands. Lanes that route through lint,
SDN config, the test runner or tooling may reach users sooner — hence a per-lane column
rather than a global disclaimer.
