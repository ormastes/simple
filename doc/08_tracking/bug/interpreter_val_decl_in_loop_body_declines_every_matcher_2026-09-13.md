# One `val` in a while-loop body declines every native matcher: 271x
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: FIXED (2026-11-11, lane interp9) — matcher accepts a leading block-local int `val`; specs green on seed. See addendum below.
- Found by: PERF-6, base `origin/main` f26970e9d93, seed sha256 `22878382bc1b5ccf...`

## Repro

Two loops, identical arithmetic, n = 2,000,000, `SIMPLE_EXECUTION_MODE=interpreter`:

```
while i < n:            while i < n:
    acc = acc + (i % 7)     val t = i % 7
    i = i + 1               acc = acc + t
                            i = i + 1
```

| shape | total us | ns/iteration |
|---|---:|---:|
| no declaration | 20,701 | **10.4** |
| one `val` in the body | 5,638,407 | **2,819** |

**271x** for the same work. The left shape is taken by one of `exec_while`'s
eleven native matchers; the right shape is taken by none of them, because every
matcher keys on a body of assignments only and a `Node::Let` disqualifies it
outright.

## Why it is filed and not fixed

This is the same family as
`interpreter_while_loop_fast_path_shape_cliff_2026-09-12.md` (PERF-1, closed by
PERF-3 at 513x/1049x), one level out: PERF-3 generalised the matched
*expression*, this is the matched *statement list*.

PERF-6 deliberately did NOT extend the matcher for it, because the frequency
does not justify the risk. `try_exec_inline_int_expr_while_loop` would only
accept `val <name> = <pure integer arithmetic over loop-local ints>` in a body
that is otherwise integer-expression assignments, and in `src/lib/common`:

- **294** in-body `val`s bind pure integer arithmetic;
- **5,887** in-body `val`s bind a call, an index, or a method result -- none of
  which the inline-int step machine can evaluate.

So the reachable population is at most 294 sites, and only those whose whole
loop body is also int-expression assignments. PERF-6 spent its budget on the
28,246-site block-scope bookkeeping instead
(`interpreter_block_scope_shadow_realloc_per_iteration_2026-09-13.md`).

The honest shape of a fix here is to treat a leading block-local integer `val`
as an extra register in the existing post-order step machine, splicing its step
list wherever the name appears -- the same mechanism
`emit_inline_int_expr`'s `bindings` parameter already implements for inlined
helper arguments. It must run LAST, after PERF-3's matcher, so already-matched
shapes keep their cheaper path.


## 2026-11-10 p2fix-interp lane (work/p2fix-interp-20261110, base d8c0a761988c) — VERIFIED-GREEN (seed-smoke)

Retained specs executed with the deployed seed bin/simple.exe
(`bin/simple test <spec> --mode=interpreter`):
while_block_local_val_parity_spec.spl 2/2
(299995 and 1333333000 in interpreter mode, interpreter==jit output);
while_block_local_val_trap_parity_spec.spl 4/4 (unused `val y = i % 0`
initializer traps identically on both lanes). Both also re-run green on a
fresh cargo build of this tree. Seed-smoke only; the 271x speed claim itself
still needs a release-seed latency measurement (not re-measured here).

## 2026-11-11 addendum (lane interp9, work/p3-interp9-20261111) — FIXED, verified on seed

Verdict: FIXED, in exactly the shape this record prescribed ("treat a leading
block-local integer `val` as an extra register in the existing post-order step
machine, splicing its step list wherever the name appears"). The fix is landed
in `parse_inline_int_expr_loop`
(`src/compiler_rust/compiler/src/interpreter_control.rs:2690`), whose first
statement now peels an optional leading `Node::Let` off the body, splices the
binding through `substitute_inline_int_local`, and declines only when the
spliced name is never read (so a trapping unused initializer like
`val y = i % 0` still traps on the generic path, exactly once per iteration).
The code comment cites this bug record by name.

Verification actually run (seed-smoke, tracked `bin/simple.exe` build-commit
`46fe8f6b6def`, `SIMPLE_LIB=src`, `--mode=interpreter --no-cache`):

- `test/01_unit/compiler/95.interp/interpreter/while_block_local_val_parity_spec.spl`
  — 2/2 PASS.
- `test/01_unit/compiler/95.interp/interpreter/while_block_local_val_trap_parity_spec.spl`
  — 4/4 PASS.
- Code inspection of `try_exec_inline_int_expr_while_loop` confirms the fix
  runs LAST among the matchers (the inline-int matcher is consulted after
  PERF-3's shapes), so already-matched shapes keep their cheaper path, as the
  record required.

Not re-measured here: the 271x latency claim itself (perf evidence was the
2026-11-10 lane's; this lane verified correctness/parity only).
