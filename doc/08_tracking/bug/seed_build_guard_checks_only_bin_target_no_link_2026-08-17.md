# `check-seed-builds-push.shs` verifies only the `--bin simple` target and never links — the Rust test suite could not build at all while every guard was green

- **Filed:** 2026-08-17
- **Status:** PARTIALLY FIXED — target-scope gap closed by a gating `--tests` leg
  plus an advisory `--examples`/`--all-targets` leg. The **link** gap and the
  **binary-staleness** gap are OPEN and are NOT closed by this change.
- **Severity:** High — this is an evidence-integrity defect, not a code defect.
  It made a green verdict mean materially less than every reader took it to mean.
- **Component:** `scripts/check/check-seed-builds-push.shs`,
  `scripts/check/check-runtime-api-regression-push.shs`
- **Related:** `doc/08_tracking/bug/origin_main_unbuildable_rust_seed_2026-08-11.md`
  (the incident that created the guard),
  `doc/08_tracking/bug/runtime_native_c_uncompilable_unsigned_box_never_implemented_2026-08-11.md`
  (the same "well-formed bytes, nonsense to a compiler" shape),
  `doc/08_tracking/bug/runtime_from_int_still_truncates_61bit_2026-08-17.md`,
  `doc/08_tracking/bug/runtime_duplicate_symbols_rust_and_c_whole_archive_2026-08-17.md`

## The measurement

At origin sha `2fb45ea1960954447acf12f769935ac83277397e`, in a clean isolated
worktree, `cargo test --release` in `src/compiler_rust`:

```
ERROR — 0 tests executed at 2fb45ea1960954447acf12f769935ac83277397e; cargo test --release cannot build the test targets
```

`TEST_RC=101` on **both** runs, rc read from a variable on the line after an
unpiped invocation. **Zero `test result:` lines in either log** — no test binary
was ever produced. Logs: `cargo_test_2fb45ea1960954447acf12f769935ac83277397e.log`
(546 lines) and `cargo_test_run2.log` (317 lines).

Corollary worth stating explicitly: a `3671 passed; 67 failed` figure circulating
today **cannot have come from origin**, because origin cannot produce linked test
binaries. It came from a contaminated tree. (Separately, that same figure was
once produced as a false `TEST_RC=0` by reading rc through a pipe.)

Meanwhile `check-seed-builds-push.shs` reported, verbatim in shape:

```
PASS — <n> file(s) checked, seed builds cleanly at <sha>
```

Both statements are true simultaneously. That is the defect.

## Three independent blind spots

The guard's verdict has been read across many lanes — including by the lane that
filed this row — as "the Rust side of this tree is healthy". It cannot support
that. There are three separate reasons, and they fail for different causes, so
closing one does not close the others.

### 1. Target scope — `--bin simple` compiles no test or example target

`run_cargo_check` (line 172) is:

```sh
( cd "$rc_dir" && CARGO_TARGET_DIR="$CARGO_TARGET_ROOT" cargo check --release --bin simple )
```

`--bin simple` compiles the binary target and the library code it transitively
uses. It does **not** compile:

- `#[cfg(test)]` modules inside the library (they are not part of a `--bin` build),
- `tests/*.rs` integration-test targets,
- `examples/*.rs` targets.

So test code that does not compile is invisible **by construction**. Note this is
a scope gap layered on top of the already-documented check-vs-build gap in the
guard's own header: even `cargo build --release --bin simple` would have missed
all three of the following, because none of them is in the `bin` target's graph.

Three real defects lived in exactly that blind spot at origin:

| # | Error | Location | Nature |
|---|---|---|---|
| 1 | `E0061` | `runtime/src/value/net.rs:773` | a `#[cfg(test)]` caller of `connect_tls_client_socket` never updated when the function gained `connect_timeout: Duration` |
| 2 | `E0599` ×2 | `runtime/tests/boxed_int_wide_roundtrip.rs:81,99` | `RuntimeValue::fits_inline_int` referenced only by that test, **defined nowhere** |
| 3 | `E0599` ×2 | `compiler/examples/m4_{asan,memprof}_probe.rs` | probe functions exist but are `#[cfg(feature = "llvm")]`; the examples carried no `required-features` |

Defect 2 is the same class as the documented `RtCoreUInt` incident: a symbol
*used* with no definition anywhere in the tree. Note that
`check-runtime-api-regression-push.shs` cannot catch that class either — it greps
for `rt_NAME(...) {` **definitions** and is structurally blind to a use of a
symbol that was never defined.

### 2. No link step — a linker error is invisible to `cargo check` by construction

The guard's header argues, correctly for its original purpose, that `check`
"runs the complete frontend and only skips codegen+link". It then treats skipping
link as harmless. It is not harmless. It is precisely how four duplicate symbols
survived in `main`:

```
rust-lld: error: duplicate symbol: rt_file_atomic_write
rust-lld: error: duplicate symbol: rt_mem_snapshot_open
rust-lld: error: duplicate symbol: rt_mem_snapshot_close
rust-lld: error: duplicate symbol: rt_mem_snapshot_record
```

Each is defined in **both** runtimes (e.g. `runtime/src/value/sffi/file_io/file_ops.rs:365`
*and* `src/runtime/runtime_native.c:9496`; the snapshot trio in
`runtime/src/mem_snapshot.rs` *and* both `runtime.c` and `runtime_legacy_core.c`).
`libruntime_sffi_c.a` is linked `-Wl,--whole-archive` under the
`runtime-symbol-table` feature (`runtime/build.rs:271`), which forces the
collision. Filed separately as
`runtime_duplicate_symbols_rust_and_c_whole_archive_2026-08-17.md`.

**Two guards, two different reasons, both blind to this one defect.** Besides
`cargo check` not linking, `check-runtime-api-regression-push.shs` evaluates the
Rust and C symbol sets **separately and never unioned** — deliberately, per its
own documentation, because unioning them masked real Rust-only removals. That
deliberate choice makes it structurally incapable of noticing that both sides
define the *same* four symbols. Neither guard is wrong on its own terms; the
union of their scopes still has a hole.

### 3. Binary staleness — guards that native-build with the deployed compiler

A third, distinct failure mode observed the same day: the deployed
`bin/simple` (59536728 bytes, mtime 2026-08-16 22:59:37) was behind origin and
failed to parse `expr_dispatch.spl` with
`Unexpected token: expected Fn, found Assign`, which origin's parser accepts.
At least 7 pre-push guards native-build compiler source with that binary. A
guard in that state emits a verdict **about the binary**, not about the change
under review — and it does so for every lane regardless of what that lane
changed. This is not fixed here and needs a binary-provenance precondition in
the affected guards (record path, size, mtime, and `--version` provenance, and
ERROR rather than FAIL when the binary is demonstrably behind the tree).

## Why this matters more than the individual fixes

The three code defects are each small. The structural consequence is not: for an
unknown number of pushes, `PASS — seed builds cleanly at <sha>` was the strongest
Rust-side evidence any lane had, and it was compatible with a tree whose entire
test suite could not build. Multiple lanes today, including the one filing this,
read it as much stronger evidence than it was and made downstream claims on that
basis. A guard that is trusted beyond its scope is worse than a guard with a
narrow, well-understood scope, because nobody re-derives the scope from the
source.

## The fix landed here, and what is deliberately advisory

Measured in an isolated worktree at the commit carrying the three code fixes
(`CARGO_TARGET_DIR` on `/mnt/data`, warm):

| leg | rc | result |
|---|---|---|
| `cargo check --release --bin simple` | 0 | the pre-existing leg, unchanged |
| `cargo check --release --tests` | **0** | clean today — safe to GATE |
| `cargo check --release --examples` | **101** before the Cargo.toml fix, **0** after | |
| `cargo check --release --all-targets` | **101** before, **0** after | |

Because `--tests` is measured clean, the target-scope gap is closed with a
**gating** `--tests` leg — it would have caught defects 1 and 2, which is the
whole point of this row. `--all-targets` is now also clean, but it is kept as a
distinct leg so that a future breakage in an `example` (a probe fixture, not
product code) reports separately and cannot silently take down the gating path.

The **link** leg is **not** gated today, and this row states that plainly rather
than pretending otherwise. Building and linking the test binaries is materially
heavier than `cargo check`, and the duplicate-symbol defect it would catch is
currently RED at origin — gating on it immediately would block every unrelated
lane and be routed around with `--no-verify` within the hour, which is worse than
an honest advisory. The path to gating it is: fix
`runtime_duplicate_symbols_rust_and_c_whole_archive_2026-08-17.md`, then promote
the link leg, exactly as `check-c-runtime-compiles-push.shs` was landed advisory
on 2026-08-11 and promoted the same day once its one real finding was fixed.

Preserved unchanged: the three-way classification (compiled / SKIP for genuinely
absent external SDK headers / FAIL), the fatal `--selftest`, the
non-vacuity contract (a run that checked 0 things is `ERROR`, never a pass), and
the existing `--bin simple` leg. rc is read into a variable on the line after
each unpiped `cargo` invocation, never through a pipe.

## Verdict convention (unchanged)

| verdict | exit |
|---|---|
| `PASS — <n> file(s) checked, seed builds cleanly at <sha>` | 0 |
| `FAIL — cargo check failed in <sha>: <first error>` | 1 |
| `ERROR — nothing was checked` | 2 |

## Open follow-ups

1. **Link leg promotion** — blocked on the duplicate-symbol row. Until then a
   duplicate symbol can still land.
2. **Binary staleness (blind spot 3)** — no guard currently asserts that the
   `bin/simple` it native-builds with is not behind the tree under review.
3. **Symbol-set union** — `check-runtime-api-regression-push.shs` should gain a
   *collision* check (a name defined in both the Rust and C sets, under
   whole-archive) as a third check alongside its removal-count and
   still-re-exported checks. That is a genuinely new check, not a widening of the
   existing separate-sets design, so it does not reintroduce the masking problem
   that design was chosen to avoid.
