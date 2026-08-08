# Bug: `verification/lean/__init__.spl` bare `export Symbol, ...` lines never import the symbols they claim to re-export — package-level `use verification.lean.{X}` fails while direct submodule import works

- **Date:** 2026-07-20
- **Status:** open
- **Area:** `src/compiler_rust/lib/std/src/verification/lean/__init__.spl`
- **Binary:** reproduced on `bin/release/x86_64-unknown-linux-gnu/simple`, which currently prints the Rust-seed bootstrap warning — this is an import/export-resolution defect, not obviously seed-specific, but not independently re-verified on a genuinely self-hosted binary.

## Symptom

`lean_block_integration_spec.spl` — all 5 examples in "Lean Block Codegen Integration" and "Lean Block Collision Detection" fail identically:

```
semantic: variable `LeanCodegenOptions` not found
```

at the first line of each test body (`var opts = LeanCodegenOptions.new()`), even though `LeanCodegenOptions` is a real, fully-defined class (`verification/lean/_Codegen/lean_codegen.spl:26`).

(An earlier tracking doc, `formal_section_failures_2026-07-18.md`, attributed this failure class to the verification modules "not existing in the codebase" — that premise is now false; the modules exist and are substantially implemented. This is a narrower, more specific defect: a broken re-export in one package `__init__.spl`.)

## Root cause

`verification/lean/__init__.spl` re-exports ~150 symbols across its ~15 submodules using bare `export Name1, Name2, ...` lines (e.g. line 73: `export LeanCodegenOptions, LeanFunction, LeanTheorem, ...`) with **no preceding `use` statement** that actually imports those names into `__init__.spl`'s own scope. Contrast with the correct pattern used by the submodule facade one level down, `verification/lean/codegen.spl`:

```simple
export use compiler_rust.lib.std.src.verification.lean._Codegen.lean_codegen.*
export use compiler_rust.lib.std.src.verification.lean._Codegen.type_builders_and_verification.*
```

`codegen.spl` correctly both imports AND exports via `export use module.*`. `__init__.spl` never does this for any of its ~15 submodules — it only lists bare `export Name` lines, which (per current re-export semantics) requires the name to already be bound in the current file's scope via a prior `use`. Since none of the ~150 names are ever imported, package-level `use verification.lean.{LeanCodegenOptions, ...}` resolves nothing.

This is why `lean_block_integration_spec.spl`'s first "LeanBlock Model" group of 5 tests pass (they import directly from the submodule: `use verification.lean.lean_block.{LeanBlock, LeanBlockPlacement}`, bypassing `__init__.spl` entirely) while the "Codegen Integration"/"Collision Detection" groups fail (they import via the package: `use verification.lean.{LeanCodegenOptions, LeanCodegen, LeanTheorem}`).

## Impact

Any consumer that imports from the `verification.lean` package root (as opposed to a specific submodule) for any of the ~150 symbols listed in `__init__.spl` lines 59-157 will hit "variable not found" at the first use. Only `lean_block_integration_spec.spl` currently exercises this path in the formal-verification test section, but the defect is systemic to the whole file.

## Suggested fix direction

Add the missing `use module.{Names...}` (or convert each bare `export Name, ...` group to `export use module.*`, matching `codegen.spl`'s already-correct pattern) for every submodule listed in `__init__.spl`.

## Repro

```bash
bin/release/x86_64-unknown-linux-gnu/simple test test/00_formal_verification/compiler/lean_block_integration_spec.spl --no-session-daemon
```
5/8 examples fail with `semantic: variable 'LeanCodegenOptions' not found` (or equivalent for other symbols reached the same way).
