# I-2 · Interpreter `[T].push` Amortized-Doubling — Done

**Track:** crypto-pure-simple-port / I-2
**Date:** 2026-04-25
**Closes:** B2 (deeper fix), H-5 (`[u64].push` quadratic, duplicate of B2)

## Summary

The B2 closure landed an `rt_bytes_alloc(n) -> [u8]` extern as a workaround
for `[u8]` bulk allocation. R-D's H-5 measurements showed the same quadratic
shape on `[i64].push` (and equivalently `[u64]`/`[u32]` since `Value::Array`
stores `Vec<Value>` regardless of element type), so the workaround alone
doesn't unblock bignum/RSA limb buffers.

This track adds the deeper fix: an in-place `Arc::make_mut(&mut vec).push()`
fast-path in the Rust-seed interpreter for `var.push(item)` / `var.append(item)`
on `Value::Array`. Because all numeric element types share `Arc<Vec<Value>>`
storage, **one site fixes every numeric vector type at once** — no per-T
parametrization needed.

## Site located (the real B2 quadratic)

`src/compiler_rust/compiler/src/interpreter_method/collections.rs:39-44`:

```rust
"push" | "append" => {
    let item = eval_arg(args, 0, ...)?;
    let mut new_arr = arr.to_vec();   // <-- O(n) copy on every push
    new_arr.push(item);
    Value::array(new_arr)             // <-- Wraps fresh Vec in fresh Arc
}
```

Empirical refcount probe at the call site (`SIMPLE_PUSH_PROBE=1`) showed
the inner `Arc<Vec<Value>>` arrives at `strong_count=3` because
`evaluate_method_call_with_self_update` evaluates the receiver, then
`evaluate_method_call` evaluates it again — naive `Arc::make_mut` would
still clone. The fix takes the value out of `env` first to drive
refcount to 1.

## Files changed

- `src/compiler_rust/compiler/src/interpreter/expr/calls.rs`
  - Added a fast-path inside the `Expr::MethodCall` arm where receiver
    is `Expr::Identifier(var_name)` and `method ∈ {"push", "append"}`
    on a `Value::Array`. Path: `env.remove(var_name)` → owned Arc with
    rc=1 → `Arc::make_mut(&mut arc).push(item)` → `env.insert(...)` +
    `MODULE_GLOBALS` mirror sync (parity with the existing slow path).
  - Gated off via `SIMPLE_DISABLE_PUSH_DOUBLING=1` for the deliberate-
    fail proof.
- `test/unit/compiler/array_push_doubling_spec.spl` *(new)*
  - Pushes 8K / 16K / 32K / 64K `i64` values via `rt_time_now_unix_micros`
    and asserts `64K_us / 8K_us ≤ 16.00`. (Linear is ~8x; quadratic is
    ~64x; the gate cleanly separates them.)

## Files NOT changed (in-scope respected)

- `src/compiler_rust/compiler/src/interpreter_method/collections.rs` —
  left as-is; the slow path is still the fallback when receiver is not
  an Identifier (e.g. `f().push(x)` or `arr[i].push(x)`).
- `src/lib/common/runtime_symbols.spl` — the user-WC modification is
  untouched per the track instructions.
- No `.spl` files outside `test/`.
- No bignum/field/sshd files.

## Scaling measurements (interpreter, Rust-seed binary)

Test command:
```
src/compiler_rust/target/bootstrap/simple test/unit/compiler/array_push_doubling_spec.spl
```

| N (i64.push) | fix-on (post) | fix-off (control) | quadratic shape |
|---|---|---|---|
| 8 192  | 23 ms   | 521 ms      |
| 16 384 | 40 ms   | 2 097 ms    | 4.0× per doubling |
| 32 768 | 79 ms   | 6 522 ms    | 3.1× per doubling |
| 65 536 | 155 ms  | 41 002 ms   | 6.3× per doubling |

**64K / 8K ratio:**
- Fix-on: **6.68×** (linear; ideal-linear = 8.0×)
- Fix-off: **78.72×** (super-quadratic; matches R-D's H-5 measurements)

R-D's H-5 repros (`/tmp/r_d_repros/h5*_u64_push*.spl`) re-measured
after fix:

| N    | R-D pre-fix wall | I-2 fix-on wall | I-2 fix-off wall |
|------|------------------|-----------------|------------------|
| 1024 | 0.04 s           | 0.013 s         | 0.031 s          |
| 2048 | 0.06 s           | 0.016 s         | 0.044 s          |
| 4096 | 0.15 s           | 0.020 s         | 0.136 s          |
| 8192 | 0.50 s           | 0.036 s         | 0.421 s          |

The fix-off column reproduces R-D's quadratic shape end-to-end (within
measurement noise); the fix-on column collapses the curve.

## Deliberate-fail proof

Test rig liveness verified by toggling `SIMPLE_DISABLE_PUSH_DOUBLING=1`:

- Default (fix on) — `PASS: ratio 668/100 <= 16.00`
- Toggle on (fix off) — `FAIL: ratio 7872/100 > 16.00 (quadratic shape)`

Test goes red on flip → green by default. Rig is live; the green is
real, not a stub no-op.

## Bootstrap rebuild

**Not needed.** This is interpreter-runtime perf, not a new extern.
Per `feedback_extern_bootstrap_rebuild.md`, full deploy is required only
when the *recognized-symbol set* changes (because the self-hosted Rust-
seed-cached release would not see the new extern). My change adds no
new symbols — just a faster `push` execution path in the Rust seed.

A `cargo build --profile bootstrap -p simple-driver` is sufficient and
was the only build step run. The Rust-seed binary at
`src/compiler_rust/target/bootstrap/simple` ships the fix immediately;
that's also what the scaling spec invokes.

## Scope limit (explicit, per advisor flag)

- This fixes the **Rust-seed interpreter** only (`src/compiler_rust/...`).
- The **self-hosted equivalent** under `src/compiler/40.eval/` (or
  wherever the pure-Simple interpreter lives) is **out of I-2 scope**
  per the disjoint-file partition. B2 doc explicitly mentions both
  layers; the self-hosted equivalent is a follow-up under "B2 deeper".
- Tests **must** invoke `src/compiler_rust/target/bootstrap/simple`
  directly — running them under `bin/simple` (self-hosted) will still
  show the old quadratic shape and must not be confused with a fix
  regression.

## Known follow-ups (not regressions)

- `self.field.push(x)` (field-access receiver) goes through a different
  code path in `expr/calls.rs:68-110`. It still uses the slow path. If
  a future bignum design stores limbs in a struct field (rather than a
  bare `var`), it'll hit the old quadratic. Easy to extend the fast-path
  here when needed.
- `pop`, `clear`, `reverse`, `sort`, `insert`, etc. are still in the
  slow path. They don't need amortized doubling for correctness, only
  for `to_vec` avoidance. Out of I-2 scope.
- The 16 module-loader / web-compiler / api-surface cargo-test failures
  observed during sanity check are **pre-existing** on this WC (verified
  by reverting my change and seeing the same failures). Not caused by
  this track.

## Acceptance gate

- [x] `cargo build --profile bootstrap -p simple-driver` clean (3m01s on
      first build, 3m30s after data-loss-corner-case patch)
- [x] `array_push_doubling_spec.spl` PASS in interpreter mode
- [x] Deliberate-fail proof flips it red
- [x] B2 quick-patch test (`test/perf/bytes_push_1mib.spl`) still works
- [x] Basic array ops (`push`, `append`, `pop`, `get`, `len`) preserved
- [~] `bin/simple build check` — invoked, returns rc=0 with empty output.
      Per `feedback_extern_bootstrap_rebuild.md`, the `build` subcommand
      is not whitelisted in the wrapper and falls through to a stale
      release binary that silently swallows output. Not a regression
      from this track. The 308 interpreter cargo unit tests passing
      (with only pre-existing module-loader failures verified by revert-
      test-restore) is the substantive `check` we can run today.

## Defensive corner case patched

Per advisor, the original fast-path had a narrow data-loss risk:
`buf.push(reassign_buf_to_int())` — argument evaluation reassigns
`var_name` to a non-Array between `matches!(env.get(...))` and
`env.remove(...)`. The fix `match`es on `env.remove` and re-inserts
non-Array results so the slow path can re-evaluate the receiver and
emit the same diagnostic it would have without the fast path.
