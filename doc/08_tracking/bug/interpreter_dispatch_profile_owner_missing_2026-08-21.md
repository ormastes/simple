# Interpreter dispatch profiler owner missing from module tree

Date: 2026-08-21

Status: REGRESSED 2026-08-22; repaired again — fresh bootstrap verification pending

## Symptom

Focused `simple-compiler` tests fail before execution with Rust `E0433` at
`compiler/src/interpreter/expr.rs`: the tracked `dispatch_profile.rs` owner is
called but is not declared by `interpreter/mod.rs`.

## Impact

The defect prevents all compiler-library regression tests, including the SFFI
return-contract and dynamic-dispatch suites, from compiling. It therefore
blocks production evidence rather than representing an SFFI semantic change.

## Fix

Declare the existing level-gated module from its canonical interpreter owner.
No profiler behavior, default state, or public interface changes.

The defect recurred on 2026-08-22 because a conflict-deduplication commit
removed what had become the last declaration. The existing guard was not wired
to any push or bootstrap entrypoint, so its source contract never executed.
The lightweight push registry now runs the guard against the exact pushed ref.

## Verification (2026-08-21)

- `src/compiler_rust/compiler/src/interpreter/mod.rs:133` declares
  `pub(crate) mod dispatch_profile;`, and `dispatch_profile.rs` is present in
  the same directory.
- `cargo check --release -p simple-compiler --lib` (dedicated
  `CARGO_TARGET_DIR`, cold, 5m07s) exits **0** with 3 warnings and no errors —
  no `E0433`, no unresolved `dispatch_profile` path. Compiling the library is
  the direct disproof of the reported symptom, which was that the crate would
  not build.

## Regression guard

`scripts/check/check-interpreter-module-owners.shs` (exit 0 = safe).

`cargo check` catches an unowned module only once a call site for it exists —
which is precisely why this defect could land at all: the file was tracked,
correct and level-gated, and nothing declared it. The guard is a text scan of
the interpreter module tree that asserts every sibling `.rs` file and every
subdirectory carrying its own `mod.rs` is declared by the owning `mod.rs`. No
compiler is invoked, so it costs milliseconds and can run on every push.

Verdict convention matches the pre-push guards: `PASS — <n> module file(s)
checked, 0 unowned` exit 0 / `FAIL — <n> checked, <k> unowned: <names>` exit 1 /
`ERROR — nothing was checked (<reason>)` exit 2. A run that examined 0 files is
ERROR, never a pass. Measured on `main`: `PASS — 12 module file(s) checked,
0 unowned`.

`--selftest` runs before every scan and is fatal (5 fixtures, all built as real
directory trees probed by the real scanner): a fully-declared tree must report
zero offenders; **the incident's exact shape** — a tracked `dispatch_profile.rs`
with no `mod` line — must be flagged; a commented-out `// mod dispatch_profile;`
must NOT count as ownership (this fixture caught a real bug in the first draft
of the matcher, which was unanchored and accepted the comment); an undeclared
subdirectory module must be flagged; and an empty tree must check 0 files so the
caller is forced to ERROR.

Honest limit: the guard proves a module is *owned*, not that it compiles or that
its call sites resolve. It is the cheap complement to `cargo check`, not a
replacement — `scripts/check/check-seed-builds-push.shs` remains the guard that
actually compiles the seed.
