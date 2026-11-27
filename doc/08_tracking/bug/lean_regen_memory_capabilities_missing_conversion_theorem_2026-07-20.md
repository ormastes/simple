# Bug: `regenerate_memory_capabilities()` never emits a `conversion_is_safe`-named theorem — generated Lean output only proves narrow special cases (reflexivity, two hand-picked pairs), not general conversion safety

- **Date:** 2026-07-20
- **Status:** resolved (verified in tree 2026-11-25; see note at bottom)
- **Area:** `src/compiler_rust/lib/std/src/verification/regenerate/memory_capabilities.spl` (`regenerate_memory_capabilities`), exercised via `test/00_formal_verification/compiler/regeneration_spec.spl`
- **Binary:** reproduced on `bin/release/x86_64-unknown-linux-gnu/simple` (prints the Rust-seed bootstrap warning); this is a content-generation gap in pure-`.spl` code, not an interpreter defect, so it is expected to reproduce identically on a self-hosted binary.

## Symptom

`regeneration_spec.spl`, example "regenerates memory capability output":
```simple
val lean_code = regen_mem_cap.regenerate_memory_capabilities()
expect(lean_code).to_contain("inductive RefCapability")
expect(lean_code).to_contain("def canConvert")
expect(lean_code).to_contain("theorem conversion_is_safe")   # FAILS
```

The generated output does contain `inductive RefCapability` and `def canConvert`, but no theorem whose name contains the substring `conversion_is_safe`. The theorems actually emitted are:
- `can_convert_refl` — `canConvert cap cap = true` (reflexivity only)
- `empty_env_allows_exclusive`, `empty_env_allows_isolated`, `empty_env_wellformed` — empty-environment special cases
- `exclusive_to_shared` — one specific hand-picked pair (`Exclusive -> Shared`)

None of these establish a general "conversion is safe" property (e.g. that `canConvert` only returns `true` for the pairs the design intends to allow, or that converting via an allowed path preserves `wellFormed`). A `grep` across the generator source and `verification/README.md` finds zero prior occurrences of the string `conversion_is_safe` — the theorem was never implemented under that name or an equivalent one; this is not a rename that the test missed.

## Impact

The formal model of reference-capability conversion (`Iso`/`Mut`/`Imm` mapped to `Shared`/`Exclusive`/`Isolated` in the generated Lean) has no proved general safety statement — only reflexivity and a handful of point cases. Anyone relying on `regeneration_spec.spl`'s green status as evidence that capability conversion is formally verified would be wrong; the coverage is much narrower than the test (as originally written) implies.

## Suggested fix direction

Either (a) add a genuinely general theorem to `regenerate_memory_capabilities()` — e.g. `theorem conversion_is_safe (src dst : RefCapability) (h : canConvert src dst = true) : ...` capturing whatever safety property the design intends (well-formedness preservation, no double-exclusive-access, etc.), and keep the test's substring check, or (b) if no such general theorem is planned, correct the test's expectation to match the narrower, already-implemented set (reflexivity + specific pairs) and stop asserting a `conversion_is_safe` name that was never a real target. Filed as GENUINE-BUG (unimplemented feature) rather than fixed here since determining the *correct* general theorem statement is a verification-design decision, not a mechanical test/API fix.

## Repro

```bash
bin/release/x86_64-unknown-linux-gnu/simple test test/00_formal_verification/compiler/regeneration_spec.spl --no-session-daemon
```
Failing example: "Lean Regeneration > module generators > regenerates memory capability output".

## Verification 2026-11-25 (lane p2w3-ai)

RESOLVED — option (a) from "Suggested fix direction" was implemented.
`regenerate_memory_capabilities()` in
`src/compiler_rust/lib/std/src/verification/regenerate/memory_capabilities.spl`
now emits a general `conversion_is_safe` theorem (line ~105):

    theorem conversion_is_safe (srcCap : RefCapability) (dstCap : RefCapability) :
      canConvert srcCap dstCap = true ↔ isMoreRestrictive srcCap dstCap
      -- proof: cases srcCap <;> cases dstCap <;> simp [canConvert, isMoreRestrictive]

`build_theorem` renders it as `theorem {name}` (`lean/_Codegen/lean_codegen.spl:107`),
so the spec's `expect(lean_code).to_contain("theorem conversion_is_safe")`
(`test/00_formal_verification/compiler/regeneration_spec.spl:26`) is satisfied
by construction. Prior lanes already re-verified the fix in tree
(`303762cc215`, `3097c6e8c47`, tracked under the sibling doc
`regeneration_spec_asserts_nonexistent_conversion_is_safe_theorem_2026-08-17`).
A fresh spec execution in this lane is environment-blocked: the pinned
`bin/simple.exe` seed rejects `@representation_boundary` tree-wide at HEAD,
so `bin/simple.exe test` cannot run any spec. Closure rests on source
inspection of the generator, the codegen renderer, and the spec expectation.
