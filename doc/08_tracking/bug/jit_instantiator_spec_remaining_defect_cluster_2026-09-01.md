# `jit_instantiator_spec.spl`: 7 remaining failures after `default()` fix — distinct interpreter/product defects

**Status:** OPEN
**Filed:** 2026-09-01
**Found by:** triage of `test/01_unit/lib/std/` failures on Windows
  (`test/01_unit/lib/std/compiler/loader/jit_instantiator_spec.spl`).

## Context

Landed fix (same triage pass): `src/compiler/99.loader/jit_instantiator.spl`
was missing `JitInstantiatorConfig.default()`, used by ~23 examples. Adding
it (mirroring the existing free function `_default_config()`'s values) took
this file from `44 total, 14 passed, 30 failed` to `44 total, 37 passed, 7
failed`. The remaining 7 are unrelated, pre-existing, distinct defects — not
touched, since each needs separate investigation:

```bash
B=src/compiler_rust/target/release/simple.exe
SIMPLE_BINARY="$B" "$B" test test/01_unit/lib/std/compiler/loader/jit_instantiator_spec.spl
```

1. **`loads metadata successfully`** —
   `expected Int(1) to match Matcher(Exact(Int(0)))` — an assertion value
   mismatch; needs reading the spec's setup to tell whether this is a wrong
   expected value in the test or a real off-by-one in the product code under
   test.

2. **`returns false for unknown symbols`** —
   `semantic: nil is forbidden by the non-optional return contract of
   'can_jit_instantiate'` — same defect signature as Cluster 1 in
   `doc/08_tracking/bug/lib_common_interpreter_typesystem_defect_cluster_2026-09-01.md`
   (a function declared non-optional returning `nil`), here in
   `can_jit_instantiate` rather than that doc's `date`/`html_entities`/`sdn`
   functions — likely the same underlying interpreter-contract-checking
   defect, different call site.

3. **`returns true for symbols in metadata`** —
   `expected Tuple([Str("test.smf"), Object { class:
   "PossibleInstantiation", ... }]) to match Matcher(BeTrue)` — the actual
   value is a 2-tuple, not a bool; looks like a genuine product bug (function
   under test returns the wrong shape) rather than an interpreter defect, but
   needs the function's source read to confirm before touching it.

4. **`returns cached code`** —
   `semantic: undefined field: unknown property or method 'code' on Tuple` —
   spec expects a `.code` field on what the product code actually returns as
   a bare `Tuple`; same family as #3 (shape mismatch between spec expectation
   and actual return type).

5. **`detects direct cycle`** —
   `semantic: type mismatch: cannot convert string to int` — distinct type
   error, uninvestigated.

6. **`adds to instantiations list`** —
   `semantic: function 'InstantiationRecord' not found` — the spec calls a
   constructor-like function `InstantiationRecord(...)` that does not exist
   under that name anywhere reachable; possibly a renamed/missing type
   (`PossibleInstantiation` exists in the same file — may be a typo/stale
   name in the spec, or a genuinely unimplemented record type).

7. **`caches JIT result`** —
   `semantic: invalid assignment: nested field access not fully supported` —
   the spec (or the product code it calls) writes through a nested field
   path (`a.b.c = ...`) that the interpreter/compiler does not support;
   compiler-internals limitation.

## Why not fixed here

Each of the 7 is a distinct defect signature needing separate,
non-mechanical investigation (some may be test bugs, some product bugs, some
interpreter limitations) — bundling a guess-fix for all of them risks
landing something wrong under time pressure. Filed together per-cluster
rather than fixed, per the "do not attempt risky compiler-internals fixes"
guidance for pre-existing/unrelated deep failures.

## Repro

```bash
B=src/compiler_rust/target/release/simple.exe
SIMPLE_BINARY="$B" "$B" test test/01_unit/lib/std/compiler/loader/jit_instantiator_spec.spl
```
