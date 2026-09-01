# HIR closure digest re-key BLOCKED: textual interface digest under-captures struct fields

**Date:** 2026-08-23
**Status:** OPEN — re-key deliberately NOT performed
**Area:** compiler / 80.driver / cache
**Severity:** perf (0% incremental HIR cache hit rate) — blocked on a correctness gap

## The waste

`hir_cache_closure_digest` (`src/compiler/80.driver/driver_hir_cache.spl:84`)
folds every surface's raw file `content_hash`. A single comment or function-body
edit anywhere in the closure therefore invalidates **all 687 HIR cache entries**.
The incremental hit rate is **0% by construction** on a phase costing ~60 minutes;
the cache only pays for byte-identical repeat builds. Source:
`doc/09_report/cache_effectiveness_audit_2026-08-23.md` (`de7c994627e`).

## Proposed fix and why it is NOT applied

Re-key the closure digest onto `interface_digest_of_source`
(`src/compiler/80.driver/cache/action_key.spl`), so only INTERFACE changes
invalidate dependents. That is only safe if the extractor is COMPLETE with
respect to downstream-visible surface. **An under-capture becomes a stale cache
HIT — a silently wrong compiler binary.** Over-capture merely over-invalidates
and is safe.

A differential spec was written first —
`test/01_unit/compiler/driver/interface_digest_differential_spec.spl` — one
interface-only edit and one paired body/comment-only edit per construct. It ran
**RED at 6 of 12** on the pre-fix extractor.

| construct | interface edit changes digest? | verdict |
|---|---|---|
| `extend` decl (retarget, methods identical) | was NO | **fixed** — `extend ` header now captured |
| re-export alias (`use m.{a as b}` + `export b`) | was NO | **fixed** — `use ` lines now captured (over-invalidates on a plain import edit; safe direction) |
| `impl` block (implementing type change) | YES | already covered |
| trait default method (signature change) | YES | already covered; default-body edit correctly does not change it |
| **struct/class FIELD retype or addition** | **NO** | **BLOCKING — not fixable in a line-prefix extractor** |

## The blocker

Fields are arbitrary indented `name: Type` lines. A line-prefix extractor cannot
separate them from body statements, match arms, dict literals or named
arguments; capturing all such lines would over-capture so aggressively that the
digest approaches the content hash and the win evaporates, and it would still
not be a *proof* of completeness against the full grammar. Field layout
(offsets, size) is directly downstream-visible, so this gap is exactly the
stale-hit class.

Per the correctness-before-speed rule, the closure digest was **left keyed on
`content_hash`**. An unfixed 0% cache is vastly better than a stale hit producing
a wrong compiler.

## Unblock path

The semantic replacement already exists and already covers fields:
`src/compiler/35.semantics/interface/compile_interface.spl`
(`simple/compile-interface/v1`, encodes `FieldSignature`), but it is
compute-and-log only and needs typed HIR / `ApiSurface`, not raw source. The
re-key becomes available once that digest is wired as the closure key. Note it
still lacks generic arity+constraints, effects, parameter passing modes and
public constants — each must be added, with a differential row here, before it
can gate a cache.

Related, out of scope here: `dep_iface_gate_*`, `needs_recompile` and
`smf_manifest_entry_verifies` have zero external callers, and nothing traverses
`src/lib/simple.sdn` `dependencies:` — no dependency-aware rebuild exists at all.
The re-key does not depend on that wiring and does not make it worth doing until
the digest is complete.

## Guard

Row `interface-digest-differential` in `scripts/check/check-perf-regression-tests.shs`
pins the spec, so a future re-key cannot land while the field gap is open.

---

## Update 2026-08-23 (second lane): the unblock path is REPLACED, and three
## shortcuts are disproven with evidence

The "Unblock path" above names `35.semantics/interface/compile_interface.spl`
as the semantic replacement. That is still a valid long-run target, but it is
**not the cheapest correct route**, and the route actually available is better.

### The real re-key target: the structured module surface

`hir_cache_closure_digest` (`80.driver/driver_hir_cache.spl:96`) already
receives `ModuleSurfacesByName` — and the surface is **already the structured
interface**, not raw text. `20.hir/hir_lowering/module_surface_types.spl`
defines `ModuleSurfaceComposite` (with `fields: [ModuleSurfaceField]`, each
carrying a full `Type`), `ModuleSurfaceEnum` (`variants: [Variant]`),
`ModuleSurfaceTrait`, `ModuleSurfaceImpl`, `ModuleSurfaceConst`,
`ModuleSurfaceTypeAlias`, and `ModuleSurfaceCallable` (with typed params and
return type). Its header states it "deliberately omits ordinary executable
bodies" — i.e. **it is already body-independent**, which is exactly the
property the re-key needs.

So the textual `source_interface_parts` extractor does **not** need to be
completed for the closure re-key, and the field gap that blocks it is
**not** on the critical path. `source_interface_parts` should be left
ALONE (it still backs SIF and the smf iface verdict, where its contract is
correct as written and as pinned).

### The genuine prerequisite: a LOSSLESS parser-`Type` encoder

Digesting the surface requires encoding each field/param/return `Type`.
**No existing encoder can be reused — all three candidates are lossy in the
stale-HIT direction.** Verified by reading them:

| candidate | why it CANNOT back a digest |
|---|---|
| `ModuleSurfaceField.type_name` / `array_element_name` scalar projections | Deliberately scalar. `Dict<text,i64>` and `Dict<text,f64>` both project to `Dict`, so a generic-argument retype digests EQUAL. |
| `module_surface_projected_type_shape` (`module_surface_declarations.spl:118`) | Returns only `named` / `array` / `other`; generic arguments are dropped by construction. Its own docstring says it is a "scalar shape class". |
| `type_to_text` (`35.semantics/lint/semantic_api/alias_registry.spl:85`) | Discriminant-guarded and otherwise close, but **unwraps modifiers**: the `Reference`, `Atomic` and `Isolated` arms all `return type_to_text(inner)`. So `&mut T`, `&T` and `T` render IDENTICALLY. Mutability and ownership are downstream-visible. It also renders `Infer`/`Error` as `""` silently. Correct for its own leaf-classifier purpose; a stale-hit generator for a digest. |

A new encoder is therefore required, over all 14 `TypeKind` variants
(`parser_types_expr.spl:53`), preserving generic arguments, `Reference`
mutability, `Pointer` constness, `Weak`/`Atomic`/`Isolated` wrappers,
`Function` arity, `Union` members and `Projection` names — and returning a
FAILURE sentinel (not `""`-as-data) on `Infer`, `Error`, or any unknown
discriminant, so the caller can fall back rather than digest a hole.

### Additional completeness constraints found (must be in the encoder, or
### the surface must fall back)

- **`ModuleSurfaceTrait.default_methods` carry full `ParserFunction` bodies**,
  and the surface header states impl lowering *injects* unoverridden defaults.
  A default-method BODY edit is therefore downstream-visible for the HIR
  cache. Note this **contradicts** the row in
  `interface_digest_differential_spec.spl` asserting a default-body edit does
  not change the digest — that row is correct for the TEXTUAL digest's
  purpose and must NOT be inherited by the closure digest.
- **`ModuleSurfaceImpl.methods` is a `Dict<text, ModuleSurfaceCallable>`** —
  keys must be sorted before folding or the digest is nondeterministic.
- **Enum struct-variant field defaults** are explicitly retained ("the one
  permitted retained expression form") and must be folded.
- **`Span` must be EXCLUDED** or the win evaporates (a body edit shifts every
  later line). The cost is that cross-module diagnostic/debug line numbers can
  go stale on a cache hit. That trade is real and is recorded here rather than
  made silently.
- Items the surface deliberately omits (param default expressions, const
  VALUES, composite field defaults) are safe to omit from the digest **only
  if** dependents cannot read them post-retention. Verify where call-site
  defaults materialise before relying on this; if they materialise at the
  CALL site, that is a fresh gap that re-blocks the re-key.

### Required shape of the change (not yet implemented)

Fail-closed **per surface**: if the encoder cannot fully encode a surface,
fold that surface's `content_hash` instead of its interface parts, and count
the fallback the way `_hir_cache_store_refusals` is counted so that a
degenerate all-fallback build is attributable rather than silent. No env
switch defaulting off — a switch that defaults off is how the mechanism ends
up wired to nothing again.

Reuse the canonical encoder: fold the parts through
`action_key.interface_digest_of`, which already exists and is already the
repo's one interface-digest scheme. Do NOT introduce a second hash scheme.

### Status

Still **OPEN**. The closure digest remains keyed on `content_hash`, which is
correct-but-slow, and the guard row pinning that is unchanged and must stay
until the encoder above exists. What this update changes is only the plan:
the blocker is now known to be a lossless `Type` encoder, not the textual
field extractor, and the three tempting shortcuts are closed off with
evidence so a later lane does not spend the discovery again.

**Not done in this update, deliberately:** no encoder, no re-key, no guard
change. A partially-validated re-key produces a silently stale compiler
binary, which is strictly worse than the 0% hit rate it would replace.

---

## Update 2: the prerequisite LANDED — lossless `Type` encoder

`src/compiler/80.driver/cache/surface_type_encode.spl` implements the encoder
the section above specified. It is **not wired to the closure digest yet** and
changes no behaviour; it is the missing building block, now present and tested.

Covers all 14 `TypeKind` variants. Preserves exactly what the three rejected
candidates lose: generic arguments, `Reference` mutability, `Pointer`
constness, and distinct tags for `Atomic` / `Isolated` / `Weak`. Free text is
length-prefixed so a name cannot collide with the delimiters around it.
`span` is excluded by design (documented trade, above).

Fails CLOSED via a `""` sentinel that is unambiguous because every success is
non-empty: `Infer`, `Error`, an unknown//future discriminant, a SIZED array
(the length is an arbitrary `Expr` and array length is layout), and depth
exhaustion all return it, and failure propagates out of any nested position.

Spec: `test/01_unit/compiler/driver/surface_type_encode_lossless_spec.spl` —
**executed=16 passed=16 failed=0** (verdict line checked for the `executed=`
count, not just `passed`). **Discrimination proved by MUTATION, not by
assertion count:** replacing the `Reference` arm with `return encoded` — i.e.
reintroducing precisely the `type_to_text` unwrap defect — turns the run
**RED at 2 of 16** (`executed=16 passed=14 failed=2`); the file was then
restored byte-identically and re-verified.

### What remains before the re-key (unchanged bar, now the ONLY step)

The surface-level encoder over `ModuleSurface`, plus the re-key itself. The
discipline it must follow, stated so it can be checked mechanically rather
than argued:

> **Enumerate EVERY field of `ModuleSurface` and either encode it, or trigger
> the per-surface fallback when it is non-empty.** A field that is neither
> encoded nor a fallback trigger is a stale-hit hole.

This was deliberately NOT attempted in this change, and the reason is
specific rather than a matter of time: three `ModuleSurface` fields —
`imports: [ParserImport]`, `exports: [Export]`, and
`ModuleSurfaceTrait.assoc_types: [AssocTypeDecl]` — have shapes that were not
verified here. The tempting shortcut is to encode the parallel scalar route
projections (`import_item_*`, `export_route_*`) INSTEAD and assume they are a
complete projection of `imports`/`exports`. That assumption is plausible (the
class comments call them "frozen route projections" and say glob expansion
reuses them) but it was **not verified**, and if it is wrong it is wrong in
the stale-HIT direction. Since every module has imports and exports, treating
them as fallback triggers instead would drive the fallback rate to 100% and
yield no win — so the assumption must be *verified*, not worked around.

Fallback shape when it is built: per surface, fold that surface's
`content_hash` instead of its interface encoding, and COUNT the fallbacks
(mirroring `_hir_cache_store_refusals`) so an all-fallback build is
attributable rather than looking like a merely cold cache. Fold the parts
through `action_key.interface_digest_of` — no second hash scheme.

Also still required at re-key time, from Update 1: `ModuleSurfaceTrait.default_methods`
carry bodies and ARE downstream-visible for this cache (fallback if non-empty),
`ModuleSurfaceImpl.methods` is a `Dict` needing sorted keys, and enum
struct-variant field defaults / variant discriminants are arbitrary `Expr`s
that must trigger fallback.

**Status: still OPEN.** The closure digest remains keyed on `content_hash`
and its guard row is untouched.
