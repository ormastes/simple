# Task #170: interpreter `Ok(v)` extraction divides multiples-of-8 by 8 -- VERIFIED, SOURCE-FIXED, DEPLOYED-STALE

**Component:** Rust seed, JIT-first Cranelift codegen path (`bin/simple run`
without `SIMPLE_BOOTSTRAP`) -- this is the seed's default execution path, not
the pure AST tree-walking interpreter (see caveat below).
**Status:** closed pending redeploy -- current seed **source** is correct;
the **deployed** 2026-07-11 `bin/release/x86_64-unknown-linux-gnu/simple`
artifact still has the bug.
**Verified:** 2026-07-17, lane S46, worktree `wt_r_fn_type`.

## Premise given to this lane (task #170)

"A global tag/box convention reconciliation (#122/#123) has landed in seed
SOURCE since [the 2026-07-11 deploy]." **The #122/#123 commits specifically
are not the fix that landed**: commits `8c52af0ece0`/`2b3c23fe004`/
`cf903fbb594`/`5ed5e0fc6de` ("fix(seed-conv): unify enum payload tag/box
convention across all construct/extract sites (#122)") are **not ancestors
of current `main` HEAD** (`662e7c7cad2` at verification time) -- confirmed
via `git merge-base --is-ancestor <sha> HEAD` (NOT an ancestor for all four
near-duplicate hashes). The helper functions that commit introduced
(`tag_enum_payload`/`untag_enum_payload_for` in
`compiler/src/codegen/instr/helpers.rs`) do not exist anywhere in the
current source tree -- this commit is an orphaned/lost commit from a
parallel lane (consistent with this repo's known force-push/rebase-race
history), not something that landed on `main`.

**The actual fix is a different, later commit: `14922f8e3cb`** ("fix(seed):
flat-nullable unwrap + nested struct pattern in enum payload (JIT path)",
2026-07-17, confirmed ancestor of HEAD). Its own commit message says it is
**not deployed** ("bin/release untouched"), which is exactly consistent
with deployed-broken / built-from-HEAD-fixed. Root cause, confirmed by
reading the code on both sides of the construct/extract boundary:

- **Extraction always assumed a tagged (boxed) payload.**
  `compiler/src/mir/lower/lowering_stmt.rs` (~line 657-686): when a value
  produced by `rt_enum_payload` (tracked via `self.tagged_vregs`) is stored
  into a concrete int/bool-typed local -- exactly what a `case Ok(v):`
  pattern-bind or a `?`/`.unwrap()` result assignment does -- MIR inserts an
  `UnboxInt` (i.e. `value >> 3`) to convert the assumed-tagged
  `RuntimeValue` back to a raw scalar. This logic pre-dates this lane's
  investigation and was not itself changed.
- **Construction did NOT box scalar payloads until `14922f8e3cb`.** Before
  that commit, `Some(x)`/`Ok(x)`/`Err(x)` construction
  (`compiler/src/mir/lower/lowering_expr_call.rs`) passed the scalar VReg
  straight into `MirInst::OptionSome`/`ResultOk`/`ResultErr` with no boxing,
  so `Ok(48)` stored the raw `48`. Extraction then unconditionally treated
  that raw `48` as tagged and applied `>>3`, yielding `6` -- exactly the
  deployed-binary symptom. `14922f8e3cb` adds
  `box_enum_payload_if_needed()`, which inserts a `MirInst::BoxInt`
  (`(value << 3) | TAG_INT`) on the scalar payload at all six
  `Some`/`Ok`/`Err`/`Option.Some`/`Result.Ok`/`Result.Err` construction
  sites, matching what extraction already assumed. After the fix, `Ok(48)`
  stores `(48<<3)|TAG_INT`, and the pre-existing `UnboxInt` at the
  extraction/bind site correctly recovers `48`.

(A secondary, same-day-in-2026-07-04, net-zero pair also touched this area:
`420bd315d87` "tag scalar payload in ResultOk/OptionSome codegen" followed
four minutes later by its own revert `6fa7130ba1c` -- both are ancestors of
HEAD but cancel out and are not the operative fix; they are a different,
lower-level (codegen `create_enum_value`, not MIR `lowering_expr_call`)
attempt at the same class of problem, tried and reverted the same week
#121/#122/#123 were active.)

## Verification: deployed binary (BROKEN) vs. freshly-built current source (FIXED)

Deployed artifact: `bin/release/x86_64-unknown-linux-gnu/simple`,
2026-07-11 08:52 UTC (the artifact named in the task). Built artifact: `cargo build --release -p simple-driver --bin simple` from `main` @ `662e7c7cad2` (fetched 2026-07-17), `CARGO_TARGET_DIR=build/cargo_s46`.

All probes run via `env -u SIMPLE_BOOTSTRAP <bin> run <probe>.spl`:

| Probe (`Ok(x)`, extraction form) | Deployed (07-11) | Built (current HEAD) |
|---|---|---|
| `Ok(48)`, `match`/`case Ok(v)` | `FAIL v=6` (48/8) | `PASS` |
| `Ok(8)`, `match` | `FAIL v=1` (8/8) | `PASS` |
| `Ok(16)`, `match` | (not run directly; see `?`-op row) | `PASS` |
| `Ok(64)`, `match` | `FAIL v=8` (64/8) | `PASS` |
| `Ok(-8)`, `match` | `FAIL v=-1` (-8/8) | `PASS` |
| `Ok(7)`, `match` (non-multiple control) | `PASS` | `PASS` |
| `Ok(42)`, `match` (non-multiple control) | `PASS` | `PASS` |
| `Ok(48)`, `.unwrap()` | `FAIL v=6` | `PASS` |
| `Ok(48)`, `?`-propagation through a wrapper fn | `FAIL v=6` | `PASS` |
| `Ok(48)`, `if val Ok(v) = get():` | `FAIL v=6` | `PASS` |

Pattern confirmed exactly as predicted: deployed binary divides every
multiple-of-8 `Ok` payload by 8 across every extraction form (`match`
binding, `.unwrap()`, `?`, `if val`), while non-multiples of 8 pass through
correctly (consistent with a spurious `>>3` applied to an already-untagged
or differently-tagged raw value). The freshly built binary from current
`main` source passes all ten probes with no changes needed.

## Conclusion

**Source-fixed, deployed-stale.** No new code fix was needed *from this
lane* -- the fix (`14922f8e3cb`, boxing scalar payloads at `Some`/`Ok`/`Err`
construction to match the pre-existing tagged-extraction assumption) already
landed on `main` on 2026-07-17, before this verification, but per its own
commit message was **explicitly not deployed** to `bin/release`. Current
`main` source already produces correct `Ok(v)` extraction for multiples of
8 (and all other tested values) through the JIT codegen path. The
2026-07-11 deployed seed binary is stale and should be excluded from use as
an oracle for `Result`-extraction-of-multiples-of-8 comparisons until
redeployed. Closes on next seed redeploy (subject to standard explicit-user-
approval gate for `bin/release` writes -- not performed by this lane per
task hard rules).

## Regression coverage added

`src/compiler_rust/driver/tests/interpreter_jit.rs`: 7 new `backend_test!`
cases (`jit_result_ok_match_extraction_multiple_of_8` and siblings, `jit`
backend only) execute construct+extract through the compiled JIT path and
assert on the actual returned `i64` value (not just symbol relocation),
covering match-binding, `.unwrap()`, `?`, and `if val Ok(v)` forms, plus a
non-multiple-of-8 control and a negative-multiple-of-8 case. All 7 pass
against a fresh `cargo build --release -p simple-driver --bin simple` of
current `main`. Scoped to `jit` (not `interp_jit`) because the pure AST
tree-walking `RunningType::Interpreter` backend SIGSEGVs on this program
shape independent of payload value -- a distinct, pre-existing,
orthogonal crash filed separately at
`doc/08_tracking/bug/interpreter_result_match_return_sigsegv_2026-07-17.md`
and explicitly out of scope for #170 (not a value-correctness bug, and
reproduces on trivial `Ok(1)` values too).

"Red" baseline for these tests is the empirical deployed-binary failure
table above rather than a literal revert-and-rerun of the Rust regression
tests, since the actual fix (`14922f8e3cb`) already landed on `main` before
this lane started and reverting it locally to reproduce "red" was judged
unnecessary extra churn in an already contention-prone shared worktree (see
Operational hazard below) given the deployed-binary A/B already supplies a
real, independently-built red baseline.

## Files

- `src/compiler_rust/driver/tests/interpreter_jit.rs` -- 7 new regression tests (task #170 section).
- `doc/08_tracking/bug/task_170_result_ok_multiple_of_8_divide_verify_2026-07-17.md` -- this note.
- `doc/08_tracking/bug/interpreter_result_match_return_sigsegv_2026-07-17.md` -- orthogonal crash filed while verifying.

## Operational hazard noted during this verification (unrelated to #170 itself)

Worktree `/home/ormastes/dev/wt_r_fn_type` was found to be **concurrently
in use by other lanes** while this verification was in progress: the shared
`refs/stash` list accumulated entries from lanes `s39` through `s48` and
`s172` with stash pushes/drops interleaving in real time (new entries
appeared between sequential `git` commands issued by this lane, and one
`git stash pop` in this lane grabbed a different lane's (`s172`) stash
entry instead of this lane's own, due to `refs/stash` being a single
repo-wide stack). The other lane's stash content
(`src/compiler_rust/compiler/src/macro/state.rs`, message
`s172-fix-temp-revert`) was restored via `git stash store` rather than
discarded. This lane's own changes were recovered read-only via the
immutable blob hash (`git show <stash-commit>:<path>`) rather than via
further stash operations, to avoid further collisions. This is an
orchestration-level hazard (worktree reuse/sharing across concurrently
running lanes) that the parent/orchestrator should be aware of
independent of this bug's resolution.
