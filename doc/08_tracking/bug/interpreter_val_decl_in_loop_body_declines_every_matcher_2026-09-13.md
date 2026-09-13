# One `val` in a while-loop body declines every native matcher: 271x

- Status: OPEN (2026-09-13)
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
