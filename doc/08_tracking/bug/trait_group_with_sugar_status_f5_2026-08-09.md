# Trait-group `with` sugar — measured status (stream F5, 2026-08-09)

Supersedes the "parser rejects `trait X with A, B:`" claim in
`src/lib/common/debug/debug_profiler.spl` (lines 15-20) and in
`trait_group_with_sugar_unwired_and_from_aot_if_val_2026-08-09.md`.
That claim was a **stale-binary artifact**, not a parser defect.

## Binary used

Built from `origin/main` @ `5b31f9e687c` in worktree
`/home/ormastes/dev/pub/simple-f5-wt`:

    cargo build --release -p simple-driver --bin simple     # 3m00s wall (cold)

    path  /home/ormastes/dev/pub/simple-f5-wt/src/compiler_rust/target/release/simple
    size  58601864
    mtime 2026-08-09 14:32:54
    banner "Simple Language v1.0.0-beta" (+ Rust-seed warning)

Deployed `bin/simple` is 29577536 @ 2026-08-09 04:50:31 — predates P0
(`50f06dcdd56`, 11:43:04). **Not modified by this stream.**

## A. Does `trait AB with A, B:` parse?

**YES.** Decisive A/B on the same source file:

| binary | result |
|--------|--------|
| new (14:32) | `PARSE_OK`, exit 0 |
| deployed stale (04:50) | `error: ... Unexpected token: expected Colon, found With`, exit 1 |

## B. Does a group compile and dispatch? — YES, and with NO desugar pass

P0 records `with` members in the **same `super_traits` field** as
`trait G: A + B` (`trait_impl_parsing.rs:40-55`), so the trait solver's
existing supertrait rule handles groups natively. Measured: a class
implementing A and B, passed as `AB`, calling both members → `sum=23`
(= 11+12), correct. Negative control (member impl removed) correctly
fails: `method 'b_id' not found on type 'C'`.

**This means the group trait feature itself needs no wiring at all.**
The desugar pass is a *separate* text-level trait implementation
(traits → struct-with-fn-fields) used only by the standalone
`app.desugar` tool. It is not a missing compiler pass.

### `G__from()` — generates and EXECUTES correctly

`test/01_unit/app/desugar/trait_group_from_execution_spec.spl`:

    SPEC FILE VERDICT ... declared>=5 executed=5 passed=5 failed=0

Caveat worth recording: the first run of this spec reported
`passed=2 failed=3`. That was a **worktree artifact** — the spec spawns
`process_run("bin/simple", ...)` and a fresh worktree has no `bin/simple`.
After symlinking the worktree's own `bin/simple` to the new binary it is
5/5. A worktree run of this spec without that symlink is a false RED.

## C. Wiring assessment — the gap is much smaller than believed

The premise "the desugar pass must be reached from a compile path" is
**wrong for the group trait itself** (B above). The only genuinely
unreachable artifact is the generated `G__from()` capability-acquisition
helper.

| option | cost | verdict |
|--------|------|---------|
| Call `desugar_traits` from the compiler | large; inverts layering (`hir_forward_lowering.spl:33-35`); would also impose the tool's struct-with-fn-fields trait model on a compiler that already implements traits natively | **reject** |
| Move the desugar tool under `src/compiler/**` | large; same model conflict | **reject** |
| Lower `G__from()` directly in the compiler as a derived assoc. fn, over native traits (not fn-fields) | moderate, self-contained; no layering inversion | **recommended** |
| Do nothing; keep `.from()` in the offline tool, hand-write acquisition | zero | acceptable interim (what backends do today) |

**Recommendation:** delete the "parser rejects" claims, convert
`debug_profiler.spl` to the `with` form once a binary carrying P0 is
deployed, and treat `G__from()` as a separate compiler-side feature.
No large refactor is warranted; no small safe wiring exists, so this
stream implemented none.

## D. `if val` AOT hazard — partially DISCONFIRMED, new blocker found

The generated capability check still uses `if val`
(`src/app/desugar/trait_desugar.spl:182`). But measured:

- Minimal case (`Option<i64>` returned by a plain fn, real `nil`):
  interpreted `NONE`, **native `NONE` too** — the documented fail-open
  did **not** reproduce on this binary.
- The actual generated shape (`Option` returned from a **fn-FIELD**,
  `src.debug_fn()`): interpreted `NONE`, but `native-build` **fails to
  compile at all** (`native-build worker exited with code 1`).

So for the generated `.from()` the AOT question is currently moot: that
shape does not reach native codegen. **Uncertainty:** I could not confirm
or refute fail-open for the fn-field shape, because it never links. The
`if val` defect may be narrower than documented, or may have been fixed
between the deployed binary and `5b31f9e687c`; not determined.

## Deploy

A deploy of a P0-carrying binary is **warranted but NOT performed** here
(per the hard constraint). Recommend it be done through the normal
bootstrap lane, not by copying this cargo artifact.
