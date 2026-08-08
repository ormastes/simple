# `var` rebind / register+list spill under the JIT — status re-check (2026-08-07)

- **ID:** native_var_rebind_register_spill_2026-08-07
- **Status:** NOT REPRODUCED TODAY — all 5 probe variants agree between engines on the currently-deployed binary
- **Severity if real:** would have been high (silent wrong numbers, no diagnostic)
- **Binary under test:** `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`,
  `Simple Language v1.0.0-beta`, self-reports as a Rust-built bootstrap seed
  (`WARNING: this Rust-built Simple binary is a bootstrap seed only`), mtime
  2026-08-07 04:52. Findings below apply to THIS binary (the seed), not
  necessarily to a freshly-bootstrapped pure-Simple self-hosted binary — see
  `.claude/rules/testing.md` binary-identity caveat.

## Origin of the suspicion

Session memory note `reference_native_list_rebind_and_spill_miscompiles.md`
(8 days old at time of this check) described, root-caused via `base58_decode`:

1. `var work = []` then rebound to a non-empty list applies a spurious `<<3`
   on later bracket-index reads.
2. `.push()` (reallocation) in one `while`-loop iteration corrupts index
   reads of the same list in a LATER iteration.

Related freestanding-lane filings describe the same mechanical shape for
scalars: `native_scalar_spill_clobber_loop_intervening_calls_2026-07-20.md`
(a `u32 val` computed before a loop and consumed inside a loop body with
~10 nested intervening calls per iteration read back wrong) — that doc
records a 2026-07-23 pure-Simple root fix in the Cranelift adapter's
block-entry value retention (kept only `Alloc` addresses, reloads everything
else from persistent stack slots) — and
`native_tuple_spill_clobber_across_call_2026-07-19.md` (tuple locals
dangled across an intervening call; fixed by heap-allocating tuple words).

## 2026-08-07 empirical re-check

Five minimal, lambda-free repros, run via `bin/simple run <file>` (engages
the Cranelift JIT by default — confirmed for each run by the ABSENCE of the
runner's `[INFO] JIT compilation failed, falling back to interpreter` log
line, which DOES appear and is visibly different when a probe has a genuine
syntax/semantic error) and again with `SIMPLE_EXECUTION_MODE=interpret`:

| # | Repro | JIT (default) | interpret |
|---|-------|----------------|-----------|
| A | `var x = 1; x = 2; x = 3; print x` (inside `fn main`) | `3` | `3` |
| B | register pressure ACROSS CALL BOUNDARIES: 18 locals bound from an opaque `mk(n)` call (so Cranelift cannot constant-fold them), summed every iteration of a 20-iteration `while` whose body also makes nested opaque calls (`burn(burn(burn(i)))`) between the definitions and the post-loop reads — the shape the 2026-07-20 freestanding filing actually needed (many live values crossing call boundaries), not just loop-local constant arithmetic | `target=25270, b1=10, b18=129` (all correct) | identical |
| C | `var xs = []` then `xs = [4, 5, 6]`, read both `xs.get(0..2)` and bracket `xs[0..2]` (memory note trigger 1; `.get()` is a runtime call, `[i]` lowers inline — both probed since they don't share a lowering path) | `4 5 6` both forms (correct) | identical |
| D | scalar spill across intervening calls inside a loop: `top`/`bottom` bound before a 30-iteration loop that calls `helper()` 3x per iteration, then reads `top`/`bottom` after the loop (shape of the 2026-07-20 freestanding filing) | `mismatches=0, top=100, bottom=40` (all correct) | identical |
| E | `.push()` inside a 40-iteration `while`, reading `ys.get(k-1)` on the SAME iteration it was pushed one index back (memory note trigger 2) | `bad=0, ys.get(0)=0, ys.get(39)=117` (all correct) | identical |

All 5/5 pass on both engines with byte-identical output. Consolidated into
one probe program with a single verdict line:
`test/01_unit/compiler/codegen/var_rebind_register_spill_jit_probe.spl` →
`VAR_REBIND_SPILL_VERDICT: pass=5 fail=0` under both `jit` and `interpret`.
Sabotage check: `_PASS` flipped to require an impossible `pass=6` in the
paired spec goes RED on both engine arms (`2 examples, 2 failures`),
confirming the assertion is not vacuous; restored to green
(`Results: 2 total, 2 passed, 0 failed`).

**Methodology note (self-correction):** an earlier pass of this check wrote
repro C/E as bare top-level statements with no `fn main`. Per
`std.spec.engine_probe`'s documented layer-3 caveat, a module with no
`fn main` de-JITs regardless of the requested engine, so that earlier run's
"JIT" column for those two repros was silently the interpreter and proved
nothing. All repros in the table above, and the consolidated probe, wrap
every case in `fn main()` and were re-verified to actually reach codegen
(confirmed by the absence of the runner's JIT-fallback log line, which DOES
fire and read differently when a probe file is malformed).

## Verdict

The originally-suspected defect does not reproduce on today's deployed seed
binary for any of the 5 probed shapes (plain rebind, register-pressure
rebind across call boundaries, empty-list-first-assignment rebind via both
`.get()` and `[i]`, scalar spill across intervening calls, loop-carried list
`.push()` spill). No claim is made here about *why* — the seed's JIT was
tested as a black box; the 2026-07-23 fix noted in
`native_scalar_spill_clobber_loop_intervening_calls_2026-07-20.md` targeted
the pure-Simple Cranelift adapter, a different lane from the Rust seed
binary actually exercised in this check, so it is not cited as the cause
here, only as background on the family.

**Not claimed:** that every variant in the 12-variant base58 shrink from the
memory note was re-tried (only the two directly cited trigger shapes were);
that the pure-Simple self-hosted `bin/release/x86_64-unknown-linux-gnu/simple`
(as opposed to today's deployed Rust seed) was checked — no bootstrap rebuild
was performed per task constraints; or that the freestanding/kernel lane
(`-kernel`/OVMF, `--entry-closure --mode dynload`) was re-verified — only the
hosted `bin/simple run` / `SIMPLE_EXECUTION_MODE` lanes were probed. The seed
is the on-lane binary for this filing (the memory note roots the defect in
seed codegen), not a fallback choice.

## Incidental finding: a SEPARATE, still-open defect (NOT this family)

While stress-testing case B's register pressure, an untyped `list`-typed
parameter element read (`fn read0(v: list) -> i64: return v[0]`) was found
to still reproduce today, independent of any preceding code — even
`fn main(): print "{read0([5])}"` alone reads back `40` instead of `5`
under the JIT (interpreter correct). This is NOT a new discovery: it is
memory note `reference_native_list_rebind_and_spill_miscompiles.md`'s
documented "THIRD trigger", already root-caused with file:line in
`doc/08_tracking/bug/untyped_list_element_read_seed_rootcause_2026-07-30.md`
(HIR `list` resolves to `Array{element: ANY}`;
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs`'s
`lower_index_expr` only emits `UnboxInt` for provably-numeric element types,
so an ANY-typed element read skips the decode entirely) and explicitly
recorded there as a deferred, cross-cutting fix (~750 danger sites,
"per-file retyping cannot responsibly cover this"). Re-confirmed open today;
deliberately NOT attempted here (high-risk cross-cutting codegen change, and
already triaged/deferred by design) and deliberately excluded from this
filing's own pass/fail count so the two independent defect families don't
get conflated in one spec's verdict.

## Regression lock-in

`test/01_unit/compiler/codegen/var_rebind_register_spill_spec.spl` +
`.../var_rebind_register_spill_jit_probe.spl`, using the out-of-process
engine-probe pattern from `f64_method_return_binop_spec.spl` /
`std.spec.engine_probe` (a `describe`/`it` spec cannot itself run under the
JIT — it spawns the standalone probe under a NAMED engine and asserts on its
stdout). `bin/simple test test/01_unit/compiler/codegen/var_rebind_register_spill_spec.spl`
→ `Results: 2 total, 2 passed, 0 failed`.
