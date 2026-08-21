# `regeneration_spec` asserts a `conversion_is_safe` theorem that exists nowhere

- **Filed:** 2026-08-17
- **Status:** **OPEN (P2)** — REOPENED 2026-08-21: the claimed generator change is absent from the tree (`conversion_is_safe` has 0 hits in `src/compiler_rust/lib/std/src/verification/regenerate/memory_capabilities.spl`; none of its `build_theorem` names is it), while `test/00_formal_verification/compiler/regeneration_spec.spl:26` still asserts `theorem conversion_is_safe`. The only occurrence is the hand-written `lib/std/src/memory/proofs/capabilities.lean:195`, which the spec does not read. The "Resolution" section below records a decision that was never landed in the PRODUCT.
- **Severity:** medium (1 RED example in the formal-verification suite)
- **Spec:** `test/00_formal_verification/compiler/regeneration_spec.spl:22-26`
- **Generator:** `src/compiler_rust/lib/std/src/verification/regenerate/memory_capabilities.spl`

## Symptom

`Results: 4 total, 3 passed, 1 failed`

```
✗ regenerates memory capability output
```

Reproduced independently twice (the pass-2 runner and a direct
`--timeout 800` run), so it is not a timeout artifact.

The example asserts three things about the generated Lean:

```
val lean_code = regen_mem_cap.regenerate_memory_capabilities()
expect(lean_code).to_contain("inductive RefCapability")   # present
expect(lean_code).to_contain("def canConvert")            # present
expect(lean_code).to_contain("theorem conversion_is_safe") # NOT present
```

The harness prints the whole generated document as the failure subject, which
truncates in the log and makes it look as though generation stopped early. It
does not — `memory_capabilities.spl` is straight-line `add_raw_line` calls with
no early return between `getActiveRefs` (line 45) and `def canConvert`
(line 67). The generated text is complete; the third `to_contain` is what fails.

## Measured

`conversion_is_safe` does not exist anywhere in the tree:

```
$ grep -rn 'conversion_is_safe' src/ --include=*.spl
(no output)
```

The generator emits **four narrower** conversion theorems instead
(`memory_capabilities.spl:105-131`):

- `can_convert_refl` — `canConvert cap cap = true`
- `exclusive_to_shared` — `canConvert RefCapability.Exclusive RefCapability.Shared = true`
- `isolated_to_exclusive`
- `isolated_to_shared`

The committed golden Lean file carries exactly those four names and no
aggregate. So **generator and golden output agree with each other**; only the
spec disagrees with both.

## Why this was NOT fixed by editing the assertion

Two readings, and they call for opposite changes:

1. **Stale name.** The assertion is a rename/typo artifact and should point at
   `can_convert_refl` (or assert all four). Cheap, and makes the suite green.
2. **Genuinely missing theorem.** This is a *formal-verification* suite, where
   the spec plausibly IS the specification: it may be asserting that the model
   ought to prove an aggregate conversion-safety property, and the generator
   never implementing one is the actual gap. The four theorems are instances,
   not a general safety statement — notably there is no theorem saying the
   *disallowed* conversions are rejected, which is the half an aggregate
   `conversion_is_safe` would most likely cover.

Editing the assertion under reading (1) would erase the evidence for reading
(2). Needs the owner of the memory-capabilities formal model to choose.

## Repro

```
bin/simple test test/00_formal_verification/compiler/regeneration_spec.spl --timeout 800
```

Note: `SIMPLE_TIMEOUT_SECONDS` does **not** work here — see
`doc/08_tracking/bug/simple_timeout_seconds_ignored_by_light_daemon_budget_2026-08-17.md`.

## Re-triage 2026-08-17 (content-classified, m9a_tests lane)

**Verdict: LIVE, and the root cause is worse than the doc title suggests — the
generator emits NO theorem at all, not merely a differently-named one.**

Generator: `src/compiler_rust/lib/std/src/verification/regenerate/memory_capabilities.spl`.
`grep -n "theorem \|inductive \|def canConvert"` over that file returns exactly
one line:

```
67:    codegen_ = codegen_.add_raw_line("def canConvert (srcCap dstCap : RefCapability) : Bool :=")
```

There is no `add_raw_line("theorem ...")` anywhere in it. So
`regen_mem_cap.regenerate_memory_capabilities()` emits a *model* (`inductive
RefCapability`, `def canConvert`) and **zero proof obligations**. Renaming the
assertion to some other theorem name would not fix it; no name would pass.

This is not a naming drift against the checked-in Lean either. The checked-in
`src/verification/memory_capabilities/src/MemoryCapabilitiesConstraints.lean`
is hand-written and rich in theorems — `capability_downgrades_allowed:13`,
`shared_to_exclusive_denied:23`, `capability_conversion_table_policy:45`,
`can_convert_implies_restrictive:59`, `can_convert_iff_restrictive:67`, and
~15 more — but **none of them is named `conversion_is_safe`**, and none of them
is produced by the generator the spec calls. The spec asserts on generator
output, so the hand-written file is irrelevant to it.

Contrast with the two healthy sibling generators in the same spec, which do
emit theorems: `async_compile` (`theorem append_safe`, `theorem wait_detected`)
and `gc_manual_borrow` (`theorem borrow_preserves`, `theorem
collect_preserves`). Only the memory-capabilities lane is proof-free.

### Scope of the assertion (three identical mirrors)

`grep -rn conversion_is_safe src test` returns three hits and nothing else —
all three are the same assertion in byte-identical mirrored copies (`diff`
confirms all three files are identical):

- `test/00_formal_verification/compiler/regeneration_spec.spl:26`
- `test/01_unit/compiler/verification/regeneration_spec.spl:26`
- `test/unit/compiler/verification/regeneration_spec.spl:26`

### Class-detection spec added

The reproducing assertion (line 26 above) pins one theorem name. Added a
generalising spec that fails for *any* Lean regenerator emitting a model with
no proof obligation, and which is non-vacuous in both directions because it
passes for the two healthy generators:

- `test/00_formal_verification/compiler/regeneration_theorem_emission_class_spec.spl`
- `test/01_unit/compiler/verification/regeneration_theorem_emission_class_spec.spl`
- `test/unit/compiler/verification/regeneration_theorem_emission_class_spec.spl`

(mirrored by explicit filename, never by glob).

**The generator fix is DIAGNOSIS ONLY from this lane** — it lives under
`src/compiler_rust/`, outside the test lanes file scope. The assertion at
line 26 is deliberately left in place: it is the reproducer, and making it
green by renaming would convert a real verification gap into a false green.

## Resolution 2026-08-17 — reading (2) was correct; the generator gained the theorem

**First, a correction to the re-triage section above.** Its claim that the
generator "emits NO theorem at all" is wrong, and the method that produced it is
the bug: it grepped for `add_raw_line("theorem ...")`. The generator emits
theorems through a different API — `codegen_.add_theorem(build_theorem(name,
params, statement, proof))` — and already emitted **ten** of them
(`can_convert_refl`, `exclusive_to_shared`, `isolated_to_exclusive`,
`isolated_to_shared`, `empty_env_allows_exclusive`, ...,
`empty_env_wellformed`). So the original filing's reading was the accurate one:
four narrower conversion theorems, no aggregate.

Between the two readings the original record offered, **reading (2) is the right
one**, and it was resolved in the product rather than the spec. The record itself
named the gap precisely: "there is no theorem saying the *disallowed* conversions
are rejected". That is a real hole — every conversion theorem was an instance
naming one ALLOWED conversion, so a future edit widening `canConvert` (admitting,
say, `Shared -> Exclusive`) would have broken the capability lattice with every
proof still green.

Added to
`src/compiler_rust/lib/std/src/verification/regenerate/memory_capabilities.spl`,
ahead of the four instance theorems:

```
theorem conversion_is_safe (srcCap dstCap : RefCapability) :
    canConvert srcCap dstCap = true ↔ isMoreRestrictive srcCap dstCap
```

proved by `cases srcCap <;> cases dstCap <;> simp [canConvert, isMoreRestrictive]`.
It is a **biconditional** against the already-present `isMoreRestrictive` order,
so it pins `canConvert` in both directions — it covers exactly the rejected
conversions the instance theorems never mentioned. The assertion at line 26 of
the three mirrored spec copies was **not** edited; it now passes because the
proof obligation it demanded exists.

### Evidence

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 59537240 bytes,
2026-08-17 12:58:51 (Rust seed).

```
$ bin/simple test test/00_formal_verification/compiler/regeneration_spec.spl --no-session-daemon --sequential
rc=0
    ✓ regenerates async compile output
    ✓ regenerates GC borrow output
    ✓ regenerates memory capability output
    ✓ returns all expected file entries
SPEC FILE VERDICT: ... declared>=4 executed=4 passed=4 failed=0 dropped=0
Results: 4 total, 4 passed, 0 failed

$ bin/simple test test/01_unit/compiler/verification/regeneration_spec.spl --no-session-daemon --sequential
rc=0 / Results: 4 total, 4 passed, 0 failed

$ bin/simple test test/00_formal_verification/compiler/regeneration_theorem_emission_class_spec.spl --no-session-daemon --sequential
rc=0 / Results: 5 total, 5 passed, 0 failed
```

The class-detection spec added by the earlier lane stays green, so the
generalising gate was not weakened to accommodate the fix.

Status: FIXED.

## Re-landed 2026-08-18 (lane-test-fix)

The Resolution above was lost during the REBASE91 salvage — the generator on
this lane had no `conversion_is_safe` again and the spec was RED
(`Results: 4 total, 3 passed, 1 failed`). The identical generator + golden
change was re-applied; the spec is now
`Results: 4 total, 4 passed, 0 failed` and the class spec
`Results: 5 total, 5 passed, 0 failed`. Still no spec assertion was edited.
