# Mission-critical allocation admission — compiler, loader, interpreter

Status: landed 2026-08-24. Audit-lane policy; the production compile path does
not consult it (see Limits).

## The problem

Under mission-critical mode the **startup seal** closes. The predicate is
`compiler.semantics.noalloc_checker.steady_state_gate_active` — sealed when
`SIMPLE_NO_STUB_FALLBACK=1` **or** the resolved `SIMPLE_SAFETY_PROFILE` is at
least `AssuranceStrictness.Critical` (`mission-critical` / `mission_critical`
are deprecated aliases for `critical`, resolved in
`src/compiler/00.common/assurance/policy_names.spl`). Once sealed,
`check_steady_state_gate` rejects every symbol whose `AllocClass` is
`Unbounded` or `Unknown`; only `None` / `InitOnly` / `BoundedPool` pass. The
governing rule is **FLT-MEM-001 "No allocation after initialization"**
(`src/compiler/00.common/assurance/flight_rules.spl:290`).

The Simple compiler, its object/JIT loader (`compiler.loader.*`,
`src/compiler/99.loader/`) and its tree-walking interpreter
(`compiler.frontend.core.interpreter.*`) all allocate on the GC heap by
construction — dynamic ASTs, symbol tables, relocation tables. Under that gate
all three are rejected outright, so none of them can run in the lane at all.

## What was already there, and what was missing

| piece | state before this change |
|---|---|
| `AllocClass` lattice + steady-state gate (`noalloc_checker.spl`) | implemented, **zero production callers** (stated at `effect_verifier.spl:376`) |
| FLT-MEM-001 | registered, and its own text says `noalloc_checker.spl` "is NOT a gate" |
| `RelaxedAllocationProfileV1` (`src/lib/nogc_sync_mut/mission_critical/domain_arena_v1.spl`) — "sealed quota transaction for **relaxed, non-critical allocation**" | implemented and spec'd, **zero production consumers** (only its own spec and `check-mci-v2-allocation.shs`) |
| an allocation field on the assurance policy | **does not exist** — `ResolvedAssurancePolicyV1` is a frozen 4-field schema with no allocation axis |
| any admission for compiler / loader / interpreter | **did not exist** |

## The port

`src/compiler/00.common/mission_critical/alloc_admission.spl` declares three
allocation domains and the sealed quota contract each is admitted under,
reusing `RelaxedAllocationProfileV1` rather than inventing a second shape:

| domain | module prefix | quota | `strict_default` |
|---|---|---|---|
| `compiler` | `compiler` | 512 MiB | `false` (the "allow alloc" posture) |
| `loader` | `compiler.loader` | 64 MiB | `false` |
| `interpreter` | `compiler.frontend.core.interpreter` | 256 MiB | `false` |

Every profile is `sealed: true`, allowed only in `ARENA_CONTEXT_NORMAL`, and
forbidden in every bit of `ARENA_CONTEXT_CRITICAL_MASK`
(kernel / ISR / storage-commit / ownership-publication / isolation-transition).

`mci_alloc_admit(module_path, context_mask)` is fail-closed at every step and
refuses with a named code: `unknown_domain`, `unsealed_profile`, `zero_quota`,
`forbidden_context`, `invalid_request`. Prefix matching is exact-or-dot-boundary,
so `compiler.loader_stub` never resolves to the loader domain; lookup is
longest-prefix, so `compiler.loader.x` resolves to `loader` and not the
enclosing `compiler`.

`compiler.semantics.noalloc_checker.check_steady_state_gate_admitted(manifest,
symbols, context_mask)` is a **sibling** of the existing gate — the original
`check_steady_state_gate` is left byte-identical, because the WP-11/WP-12
regression specs pin it as the unadmitted baseline. The sibling skips a
violation when the symbol's registered `family_module` is admitted.
`check_steady_state_gate_admitted_normal` is the `ARENA_CONTEXT_NORMAL` form.

## Limits — read before citing this as a bound

* **Admission, not enforcement.** The admitted subsystems allocate through the
  ordinary GC heap; they are **not** routed through a `domain_arena_v1` arena,
  so `quota_bytes` bounds nothing at runtime. An admitted domain is
  "admitted-unbounded under a sealed quota contract".
* **No reclassification.** An admitted symbol keeps its `AllocClass`, including
  `Unbounded`. Calling it `BoundedPool` without arena routing would be a false
  claim, and the spec pins that it is not done.
* **Audit lane.** Like `noalloc_checker.spl` itself, nothing on the production
  compile path calls this. Wiring it into a live compile gate is separate work.

## Evidence

* Gate: `sh scripts/check/check-mci-alloc-admission.shs` →
  `PASS — 14 case(s) checked, 3 domain(s) admitted (compiler, loader, interpreter), all refusals intact, unadmitted baseline unchanged` (exit 0).
  `--selftest` (5 fixtures: identical-must-pass, flipped-verdict-must-fail,
  widened-admission-must-fail, regressed-baseline-must-fail, empty-must-check-zero)
  runs first and is fatal.
* Spec: `test/01_unit/compiler/mission_critical/alloc_admission_spec.spl` →
  `Results: 16 total, 16 passed, 0 failed`.
* Unchanged baseline: `test/01_unit/compiler/semantics/noalloc_alloc_class_spec.spl`
  → `Results: 9 total, 9 passed, 0 failed`.
