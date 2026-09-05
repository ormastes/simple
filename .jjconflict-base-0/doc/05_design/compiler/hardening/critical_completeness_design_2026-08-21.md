# Critical Completeness Design — static / complete / dyn, Any boundary, typed monomorphization, aspect seal

**Date:** 2026-08-21
**Source research:** `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md` (sections 5–13, 18)
**Companion plan:** `doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md`
**Scope:** design only. Every landing site below was verified against this tree; where the
research doc's §9.1 "current source state" no longer matches, this document states the
current truth with `file:line` evidence instead of copying it.

---

## 0. Stale claims in the research doc (corrected here)

The research doc was written against revision `d200f577aaa`. Monomorphization work landed
after that snapshot. §9.1 claims that must NOT be carried forward:

| §9.1 claim | Tree today |
|---|---|
| "`MonomorphizationTable` stores pending and specialized functions/structs/classes as `Any`" | **False.** `src/compiler/40.mono/monomorphize/table.spl:29` `pending_functions: [(SpecializationKey, FunctionDef)]`, `:39` `specialized_functions: {SpecializationKey: FunctionDef}`. `grep -n Any table.spl` returns nothing. The table is already typed. |
| "`process_specializations()` explicitly skips real specialization" | **False.** `src/compiler/40.mono/monomorphize_integration.spl:433-451` calls `process_pending()`, then for each pending mangled name builds `specialize_function_with_types(template, spec_type_args)`, clears `type_params`, assigns a fresh `SymbolId` (`:448`) and counts `stats.specializations_created` (`:450`). |
| "`rewrite_module()` returns the module unchanged" | **False.** `monomorphize_integration.spl:457+` adds specialized definitions and repoints call sites; the real rewrite walk is `rewrite_expr` (`:527`) covering `Call` (`:540`), `MethodCall` (`:572`), `Binary` (`:577`), `Unary` (`:581`), `Return` (`:586`), and `rewrite_stmt` (`:512-519`). |
| "`substitute_type()` and `substitute_expr()` are identity functions" | **False for types.** `src/compiler/40.mono/monomorphize/type_subst.spl:74-128` recurses through `TypeParam, Tuple, Array, Slice, Dict, Ref, Ptr, Optional, Isolated, Result, Named, Union, Function`. |
| "`concrete_to_hir_type()` returns `HirTypeKind.Error`" | **Superseded**; the function now exists at `type_subst.spl:32` as a real conversion. Re-audit before quoting. |

**Claims that remain TRUE and are load-bearing for this design:**

- `src/compiler/20.hir/match_coverage.spl:36-41` — `ResolvedMatchCoverage.is_exhaustive()` returns
  `true` immediately when `self.has_wildcard`, and `missing_variant_ids()` (`:43-46`) short-circuits
  to `[]` under a wildcard. A `_` arm therefore *defines away* coverage.
- `type_subst.spl:127` still ends with `case _: ty` — a wildcard closing the type-substitution match.
- `src/compiler/35.semantics/safety_checker.spl` still contains **10** `case _:` arms.
- `src/compiler/80.driver/driver_hir_pipeline_passes.spl:82` `run_typecheck_warn_pass` and `:146`
  `run_safety_warn_pass` are, by their own doc comments (`:98`), **FAIL-OPEN** warn passes.
- No `hir_type_to_mir` / `lower_hir_type` symbol exists in `50.mir`; type lowering is spread over
  `mir_lowering_types.spl` (which still uses an `HirTypeKind.Error` sentinel, `:124`). The
  open bug `doc/08_tracking/bug/mir_lowering_missing_hirtypekind_arms_wildcard_fatal_2026-08-05.md`
  stands.

---

## 1. Three semantic states, two independent axes

Semantic **closure** is orthogonal to **linkage** and to **activation**.

```
closure:    static | complete | dyn        # when the constructor universe closes
placement:  static_link | dynload          # how the code arrives
activation: startup | first_use | command | manual | hotspot
capability: off | auto | on
```

| State | Universe closes | Exhaustiveness point | Critical | Dispatch |
|---|---|---|---|---|
| `static` | source / compiler build | compile time | yes | direct switch |
| `complete` | config / link / seal | seal + generated compile check | yes | dense frozen table |
| `dyn` | never while running | per-registration contract only | no (must be frozen to `complete` first) | registry |

Critical restrictions: `dyn` rejected; `first_use` only for content already verified and sealed;
`hotspot` rejected for any semantics-changing module or aspect.

**Landing site:** new `src/compiler/00.common/completeness/**` (closure enum, seal record) and
`src/compiler/00.common/dynamic_identity/**` (persistent ids). Neither directory exists today —
they are created by Wave 0/1.

## 2. Grammar: `complete:` / `dyn:` enum sections

```simple
enum ExprKind:
    Int(i64)
    Call(Expr, [Expr])
    complete:
    dyn:

extend ExprKind:
    complete:
        async.Await(Expr)
        gpu.KernelLaunch(KernelAst)
    dyn:
        ide.LiveProbe(ProbePayload)
```

- an enum with neither section is closed;
- the original static ordinal sequence is never renumbered by an extension;
- payload schema change requires an ABI-version bump.

Match semantics:

```simple
match expr.kind:
    case Int(v): ...
    case Call(c, a): ...
    case complete ext: ext.require<HirLower>().lower(self)
    case dyn ext: unsupported_dynamic_expr(ext.identity)
```

`case complete` covers only the frozen complete region and is legal only when the binding carries a
verified required interface; `case dyn` covers only the open region; **neither covers a missing
static constructor**, so adding a static variant still breaks the match. In critical, `case dyn` is
unreachable by policy and is rejected at seal time.

**Landing sites:** declaration parsing in the enum-declaration path of `src/compiler/10.frontend`;
match arms in the pattern path; the resolved record extends
`src/compiler/20.hir/match_coverage.spl` — `ResolvedMatchCoverage` gains
`complete_covered_by_interface: bool` and `dyn_arm_present: bool`, and `is_exhaustive()`
(`match_coverage.spl:36`) must stop treating `has_wildcard` as sufficient under `@exhaustive` /
critical. That single early-return is the highest-value edit in this design.

## 3. Wildcard policy and the coverage witness

```
E-COMPLETE-001: wildcard cannot close an @exhaustive compiler-IR match
```

Witness sets, computed at compile/seal time (not runtime):

```
StaticRequired(E)   - StaticCovered(match)              = {}
CompleteRequired(E, seal) - CompleteCoveredOrInterface  = {}
DynamicReachable(E, seal)                               = {}   # critical only
```

## 4. CoverageState and the negative-space checker

```simple
enum CoverageState:
    Implemented
    Normalized(target: StableVariantId)
    Unsupported(reason: text, issue: text?)
    NotApplicable(reason: text)
```

`Missing` is not a checked-in state — it is the result of set subtraction:

```
Missing = ProducerUniverse - Implemented - Normalized - Unsupported - NotApplicable   # must be {}
MissingCapabilities = RequiredCapabilities(ctor) - ProvidedCapabilities(ctor)         # must be {} at seal
```

Boundaries covered: grammar→FlatAst, FlatAst→AST, AST→HIR, HIR→MIR (type/expr/stmt),
MIR→interpreter (`95.interp`), MIR→LLVM, MIR→Cranelift.

**Landing sites:** new `src/compiler/00.common/transition/**` (the enum + validator + SDN reader);
per-boundary declaration files generated, not hand-written; the HIR→MIR type row set is the
existing gap in `src/compiler/50.mir/mir_lowering_types.spl` and `_MirLowering/function_lowering.spl`.
Surface as `simple compiler coverage [--profile=critical] [--stage ...] [--format=sdn]` under
`src/compiler/90.tools/`, wired in `src/app/cli/dispatch/table.spl`.

## 5. Identity: persistent vs dense

Never allocate identity by load order, and never serialize the dense tag.

```
PersistentExtensionId = (owner_enum SymbolId, provider module SymbolId,
                         constructor local ordinal, payload schema ABI version)
ProcessLocalTag       = dense index assigned only after the static+complete freeze
```

After seal, static and complete variants are reindexed into one dense range
(`0..static_count-1`, `static_count..sealed_count-1`, `DYN_MARKER+registry_index`) so complete
dispatch costs the same as static (§18.1 of the research doc). Serialize the persistent tuple,
payload schema version, payload hash, and the complete-universe seal hash — never the tag.
Seal-time rejections: tag-capacity overflow, provider-local id reuse, persistent-id collision,
payload size/alignment overflow, unbounded recursive payload, 32-bit layout mismatch, and a
stable-id tuple that disagrees with its claimed hash.

## 6. `Any`: unsafe `type_erasure` boundary + AnyEscapeChecker

Rule: in `critical`, `Any` is illegal in safe code; legal only lexically inside
`unsafe(reason: ..., capabilities: [type_erasure])`, and no `Any` value may leave that block.

```simple
unsafe(reason: "decode legacy plugin payload", capabilities: [type_erasure]):
    val raw: Any = legacy_plugin.read()
    val decoded: PluginMessage = checked_decode<PluginMessage>(raw)?
```

`AnyEscapeChecker` runs after HIR type resolution and is dataflow-aware (a source-text lint is
insufficient). Origins: literal cast, FFI return, dyn plugin return, erased container read,
reflection. Critical errors: `Any` created outside the capability; stored in a field/global/container;
returned or yielded; captured by closure/coroutine; live across `await`/`yield`; passed to a
non-unsafe function; sent to task/process/device; any operator applied directly; leaving the
boundary without a checked conversion.

Migration order when removing an `Any`: monomorphized generic → closed sum → typed interface →
validated `WireValue` → opaque `newunit` handle → unsafe boundary (last resort).

**Landing sites:** new `src/compiler/35.semantics/any_escape/**`, invoked from the HIR pipeline
next to `run_safety_warn_pass` (`driver_hir_pipeline_passes.spl:146`) — but as a **deny** pass under
critical, not the fail-open warn shape documented at `:98`. Capability schema extends
`src/compiler/00.common/assurance/**`.

## 7. Typed monomorphization

`MonoSemanticKey` = (definition StableSymbolId, type_args, const_args, effect_args,
capability_args). `MonoArtifactKey` = semantic key + target triple + data-layout hash + CPU-feature
hash + backend id + assurance-semantics hash + complete-universe hash + weave-plan hash.
Diagnostics-only policy stays out of the semantic key.

The table is **already typed** (`table.spl:29,39`); the remaining work is (a) replacing
`SpecializationKey` with `MonoSemanticKey` so const/effect/capability args participate, and
(b) the fixed point. Algorithm: typecheck templates → resolve complete/aspect config and weave →
discover roots (exports, entrypoints, statics, complete-extension handlers, aspect advice/facet
entrypoints, required witnesses/vtables) → scan → canonicalize → dedup by key → clone + recursively
substitute → insert with a stable mangled symbol → rewrite references → rescan → repeat → mark
templates non-emittable → verify → lower.

Post-mono invariants, all required to be zero: unresolved `TypeParam`; generic
call/constructor/method; generic emitted definition; `Any` introduced as erasure;
`HirTypeKind.Error` created by substitution; unknown type mangling; unresolved associated
projection; target-width-ambiguous layout; missing drop/witness/vtable instance.

Substitution must be *exhaustive*, which is exactly what `type_subst.spl:127`'s trailing
`case _: ty` prevents: a new `HirTypeKind` variant silently substitutes to itself. Replace it with
named arms plus a generated visitor so a new variant fails the compiler build.

**Landing sites:** `40.mono/monomorphize/{table,type_subst,rewriter}.spl`, new
`40.mono/monomorphize/hir_subst/**`, new `40.mono/monomorphize/collector/**`, new
`40.mono/verify/**`; the driver call is `monomorphize_impl` (`driver_hir_pipeline_passes.spl:53`) —
the integrator alone edits that file and only relaxes the existing loud generic-native gates after
the verifier is green.

Dynloaded generic code: either a pre-specialized sealed manifest, or template + trusted compiler
service (non-critical only, or the critical compiler regenerates, verifies, signs and extends the
seal). Code-size controls: canonical type ids, dedup, COMDAT/link-once, per-package specialization
budgets, recursion-depth and growth-factor limits, size reports in the manifest. A rejected budget
never silently falls back to `Any`.

## 8. Aspect seal and lifecycle

```simple
enum AspectState:
    Catalogued
    Resolved
    Verified
    Loaded
    Staged
    Bound
    Sealed
    Active
    Failed(AspectError)
```

Critical rules: no `Active` → unloaded for semantics-bearing aspects; nothing published before every
required binding is staged; one generation published atomically; failed activation publishes
nothing; no aspect added after seal; first-use loading may map/decompress verified content but
cannot change the seal.

The seal contains: selected aspects+versions, pointcut expansion result, matched joinpoint ids,
advice ordering and conflict resolution, facet bindings by concrete type, required witness handlers,
effects and unsafe capabilities, base/public/layout ABI hashes, module/content/index/signature
hashes, weave-plan hash, post-weave HIR hash, proof references, activation policy.

Advice-mode cost (§13.6/§18.6): omitted = zero; explicit facet acquisition = zero until called;
static weave = normal woven cost; sealed complete patchpoint = arch NOP/guard, critical **only if in
the seal and measured**; open dyn patchpoint and hot reweave = not critical.

**Landing sites:** build on the existing aspect-pack catalog/container slice rather than replacing it
(see `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md` and
`doc/09_report/aspect_pack_design_coverage_2026-08-18.md`); new `99.loader/completeness_seal/**`;
critical aspect policy checker under `00.common/assurance/**`.

## 9. Pipeline ordering and normalization barriers

```
1 resolve profile/config -> 2 parse -> 3 validate grammar/FlatAst/AST transitions
-> 4 lower to typed HIR -> 5 resolve names/types/effects/ownership
-> 6 safety/unsafe/Any checks -> 7 resolve complete extensions + aspects
-> 8 verify manifests/ABI/handlers/effects/deps/signatures -> 9 weave + normalize typed HIR
-> 10 RE-RUN type/effect/ownership/safety on woven HIR -> 11 monomorphization fixed point
-> 12 post-mono verifier -> 13 normalization barrier -> 14 canonical MIR
-> 15 MIR structural/transition/safety verifier -> 16 optimize under preservation contracts
-> 17 interpret canonical MIR as reference -> 18 JIT/native -> 19 differential validation
-> 20 artifact + evidence seal
```

Aspects must be resolved **before** final monomorphization (step 9 < step 11) because typed weaving
introduces generic advice calls, new witness/vtable requirements, changed effects/capabilities, new
control-flow edges, and new unsafe boundaries — mono and the safety closure must see the post-weave
program.

Barriers by stage: source AST = static+complete+dyn as the profile allows; typed pre-weave HIR =
static+complete (dyn only outside critical); canonical post-mono HIR = static core plus explicitly
permitted frozen complete dialect ops; canonical MIR = closed static core or a finite sealed backend
dialect set; machine IR = backend-sealed dialect. Prefer normalizing an extension to a core
operation before MIR; keep a dialect op only when normalization would destroy required semantics.

**Landing site:** the ordering above is enforced in `driver_hir_pipeline_passes.spl` — today it holds
`resolve_methods_impl` (`:30`), `type_check_impl` (`:47`), `monomorphize_impl` (`:53`),
`run_typecheck_warn_pass` (`:82`), `run_safety_warn_pass` (`:146`). Steps 7–10 and 12–13 have no
representation there yet.

## 10. Forbidden shapes

```simple
case _: NilLit        case _: Error        case _: pass
case _: 0             case _: scalar_fallback(...)
```

Allowed only when the wildcard is over an explicitly open `dyn` region and the action is typed
dynamic dispatch or an explicit diagnostic. The coverage report is generated from the manifest and
can never be hand-maintained — a stale "complete" document does not satisfy a release gate.
