# Lane-local Rust seed unbuildable: REBASE91 salvage re-introduced a stale `INLINE_INT_BITS` block

- **Status:** PARTIALLY REPAIRED 2026-08-18 — E0592 fixed; the seed still does
  not compile for two OTHER pre-existing reasons (below). Bootstrap remains
  blocked in this lane.
- **Date:** 2026-08-18
- **Area:** `src/compiler_rust/runtime/src/value/core.rs` (lane-local),
  `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`
- **Scope:** **This lane only. `origin/main` is healthy** — verified, see below.
- **Found while:** trying to close the bootstrap evidence gap left by the
  deletion of `src/compiler/50.mir/custom_primitive_bitfield.spl`.

## Scope first, because the initial read was wrong

An investigation pass reported this as "the Rust seed does not compile at HEAD"
and suggested someone should fix it repo-wide. That framing is **incorrect** and
is corrected here:

```
$ git show origin/main:src/compiler_rust/runtime/src/value/core.rs | grep -c 'pub const INLINE_INT_BITS'
1        <- origin/main: healthy, one definition
$ grep -c 'pub const INLINE_INT_BITS' src/compiler_rust/runtime/src/value/core.rs
2        <- this lane: two
```

The duplication is local to this lane's branch, inherited from the REBASE91
salvage commits (`ec35449db2c`, `fa8df855783`) that predate the current session.
No other lane is affected by it, and nothing needs pushing to fix origin.

## The defect

Two definitions of `INLINE_INT_BITS` / `fits_inline_int`, which `cargo check`
rejects:

```
error[E0592]: duplicate definitions with name `INLINE_INT_BITS`
   --> runtime/src/value/core.rs:335:5
error[E0592]: duplicate definitions with name `fits_inline_int`
   --> runtime/src/value/core.rs:354:5
```

They are **not** identical copies — that is the important part. They are two
contradictory generations of the same code, and a merge landed both:

| block | lines | what its doc comment asserts |
|---|---|---|
| A | 304-330 | "`from_int` above **now consults it**: values outside the range are heap-boxed via `from_wide_int` … `boxed_int_wide_roundtrip.rs` is the oracle and is **GREEN**" |
| B | 335-361 | "`from_int` above **does NOT consult it** — it shifts unconditionally and never heap-boxes, so wide values are still truncated … the wide-int tests are **expected to be RED** against this file; that is the point" |

Block A is the post-fix state; block B is the stale pre-fix state that
`4e265503e0c` ("drop duplicate INLINE_INT_BITS/fits_inline_int — origin already
defines both") had already removed once, and that the salvage merge reinstated.

A naive "delete the duplicate" would have been a coin flip on the runtime's
integer semantics: keeping B would have silently reverted 61-bit wide-integer
boxing across the whole runtime.

## Repair

Block B (lines 330-359) deleted, keeping block A. Chosen because origin/main
contains **exactly** block A — verified rather than reasoned about:

```
$ diff <(git show origin/main:.../core.rs | sed -n '295,340p') <(sed -n '295,340p' .../core.rs)
REGION MATCHES ORIGIN EXACTLY
```

`cargo check --release --bin simple` afterwards: **`E0592` count 0**, and
`simple-runtime` compiles.

## Still blocked — two unrelated, pre-existing errors

The seed still does not build, for reasons that have nothing to do with either
this repair or the `custom_primitive_bitfield.spl` deletion:

```
error[E0432]: unresolved import `crate::interpreter::module_globals_generation`
error[E0599]: the method `as_ref` exists for reference `&simple_parser::FunctionDef`,
              but its trait bounds were not satisfied
error: could not compile `simple-compiler` (lib) due to 2 previous errors
```

`module_globals_generation` is imported by
`compiler/src/interpreter_call/core/function_exec.rs:10` (used at `:115`,
`:195`) but is not defined in this lane's `interpreter` module. This is the
consumer half of another lane's in-flight change (compare simple-main's HEAD
`47411747677`, "fix(interpreter): mirror method-call self-updates into
MODULE_GLOBALS") salvaged in without its producer. Resolving it means importing
that lane's work, which is explicitly **not** done here — this lane must not
guess at another lane's half-landed change.

## Consequence for the deletion evidence gap

**Still OPEN.** `bin/simple build bootstrap` cannot be attempted in this lane
until the seed compiles. The preflight gate says so directly:

```
FAIL — 5 check(s) run, failing: cargo-check (0 skipped)
```

So the deletion's evidence remains what it was: the compiler's modules load and
AC-5/AC-6 behaviour is intact (`custom_primitive_sffi_spec.spl` 20/20,
`bitfield_mir_spec.spl` 14/14). A from-scratch self-hosted rebuild is still
unproven. Note symmetrically that this unrelated seed breakage does **not**
vindicate the deletion either.

Two further practical blockers, recorded but not forced: `bin/simple` here is a
symlink to the SHARED seed binary used by other lanes and must not be rebuilt or
replaced, and this worktree has no `build/` directory at all (cold cache,
multi-hour full rebuild).
