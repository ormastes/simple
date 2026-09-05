# Gate validation: check-seed-native-build-invariant.shs

Repo state: HEAD = 0e7124b9089 (main). No commits/pushes made. No bootstrap/stage4 run — only
seed (Rust `cargo`/existing binary) native-build invocations.

## Seed used (proven good, per task's own criteria)

`src/compiler_rust/target/bootstrap/simple` (pre-existing on disk, built 2026-07-25 04:21 UTC by a
concurrent session from a tree at/after HEAD).

- `git merge-base --is-ancestor 3e92fc115116 HEAD` → YES (CompiledSymbolKind fix present)
- `strings -a <seed> | grep -c rt_string_new_literal` → **4**
- Trivial single-file native-build (`print(3+4)`) → builds, runs, prints **7**, rc=0

This satisfies the "known-good seed" bar given in the task.

## Task 2: does the gate PASS against the known-good seed? **NO**

```
sh scripts/check/check-seed-native-build-invariant.shs src/compiler_rust/target/bootstrap/simple
```
→ `FAIL seed-native-build-invariant  seed native-build FAILED (rc=1) ...`

Root cause (captured full build.log, not just the script's 40-line tail):
```
[ERROR] MIR error: MIR lowering error: undefined variable: ITEMS
[STDERR] error: MIR lowering error: undefined variable: ITEMS
```

This is **not** the cross-module lazy-import/aliasing bug the fixture and gate comment describe
(no "array index out of bounds", no wrong printed value — it never gets that far). It fails at
MIR-lowering time, before the interpreter's module-global aliasing path the historical fix
(5d9e9b7251b, 07adf0c25f4, etc.) touches is ever reached.

### Isolating the real cause

Three throwaway repros, same seed:

1. Fixture as shipped (2 modules, `use owner.{owner_items}`, module-level `val ITEMS: [i64]`) → **FAIL**, `undefined variable: ITEMS`.
2. Same code collapsed into **one file, no import at all** (`val ITEMS: [i64] = [2,3]` + a function
   reading it) → **FAIL**, identical error. Proves this has nothing to do with cross-module
   resolution or the `use owner.{owner_items}` import spelling — the import form is fine.
3. Same shape but `ITEMS` inlined as a literal (`[2, 3]`) instead of a module-level `val` → **PASS**, prints 5.
4. Module-level **scalar** `val N: i64 = 5` (no array) → **PASS**, prints 5.

Conclusion: native-build's MIR lowering currently cannot resolve a module-level `val` global of
**array type** at all — same-module or cross-module makes no difference, and this is independent of
whichever seed (good or bad w.r.t. the lazy-import regression) is used. The fixture happens to pick
an array-typed module global, so it trips this unrelated, still-open gap before it can ever exercise
the invariant it was written to protect.

## Task 3: decisive test (fail on a buggy seed) — **not meaningfully answerable as designed**

Because the fixture fails at a compile stage common to every seed regardless of the interpreter-level
aliasing fix's presence, it cannot discriminate "seed has the lazy-import bug" from "seed doesn't" —
it fails identically either way. Building an actual pre-fix seed (e.g. at `d312b8e4253` or its
immediate successors) is also confounded by NOT having the `3e92fc115116` CompiledSymbolKind fix
(all commits between `d312b8e4253` and HEAD lack it — `3e92fc115116` lands after all of them), so a
literal "seed at an old commit" run would fail for a third, unrelated reason. Given repro #2 above
already shows the fixture fails unconditionally, spending a build cycle on that seed would not add
information — the fixture cannot pass in its current form on **any** seed, so it cannot possibly be
shown to selectively fail on a buggy one.

**This is a gate that cannot currently pass at all — worse than "theatre that always passes": it is
theatre that always fails, for a reason unrelated to its stated purpose.** It would block every
commit if wired in, regardless of the actual invariant's health.

## Runtime

Single native-build attempt against the fixture (fails fast, at MIR lowering, before codegen/link):
~2-3s wall. The trivial-script control case (full success path: parse → MIR → codegen → link →
run) took under the 60s `BUILD_TIMEOUT_SECS` budget comfortably (finished in well under a minute
including stdlib/runtime-bundle compilation). Diagnostics ARE clear and correctly named ("MIR
lowering error: undefined variable: ITEMS") — the gate's failure message and log tail successfully
surface the real Rust-side error text, that part of the harness works as designed.

## Recommendation: **REDESIGN, do not wire**

1. Do not wire this gate into pre-commit/`bin/simple build check`/CI in its current form — it is
   permanently red and would block unrelated work.
2. File a bug: "native-build MIR lowering fails to resolve module-level array-typed `val` globals
   (`undefined variable: <name>`)" — reproducible in a single file with zero imports. This is a real,
   separate defect from the lazy-import regression this gate was chasing, discovered as a side effect
   of this validation.
3. Rebuild the fixture around a shape that (a) actually native-builds successfully today given every
   landed fix, and (b) is falsifiable against a seed that only lacks the specific interpreter aliasing
   fix. Candidates: avoid module-level array `val`s entirely (e.g. use a module-level function that
   returns a literal array, or a scalar global, for the "shared owner state" the reader observes) so
   the fixture exercises cross-module identity/aliasing without tripping the MIR-lowering gap.
   Re-validate both directions (pass-good / fail-bad) before ever proposing a wiring point again.
4. Until step 3 lands, the gate script itself (harness, timeout handling, diagnostics) looks sound and
   can be kept as-is — only the fixture needs replacing.
