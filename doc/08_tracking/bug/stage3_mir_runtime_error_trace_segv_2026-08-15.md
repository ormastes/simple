# Stage 3 MIR lowering SIGSEGV after RuntimeError call trace

Status: open; diagnostic owner not yet proven. Three-cycle bootstrap fix cap reached.

The final bounded Stage 3 retry used admitted Stage 2 compiler
`042b35c2ef8c2f74f2b1f2497ba2c8acd3830e035cccdc3a6feac342b3ba5844`
and the exact staged runtime authority. It completed source closure 604/604,
parse 604/604, and HIR with zero recorded failures. The earlier
`current_core_lexer` and `_expr_13` unresolved-static diagnostics did not
recur.

The compiler then terminated with SIGSEGV status 139 during MIR lowering. The
outer controller recorded only:

```text
Segmentation fault (core dumped)
```

No core, instruction pointer, candidate, sanity receipt, or Stage 3 cache
object was retained. Elapsed time was 11:08.09 and peak RSS was
14,189,260 KiB. The Stage 3 native log ends after repeated successful trace
markers for `RuntimeError` method-call lowering (including
`method-dispatch-after`, `impl-return`, and span restoration) with local IDs
20, 57, and 62. That establishes the last observed work only; it does not
prove that `RuntimeError`, method dispatch, or the next unlogged operation is
the crashing owner.

Retained evidence:

- controller/status/time:
  `build/native_probe/stage4-owner-20260815/canonical-stage3-top-level-expr-final.{log,status,time}`
- native log:
  `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
- progress:
  `build/bootstrap/bootstrap-build-progress.events`
- controller SHA-256:
  `26d422b0a44e4f756144e1c3fde97aaeb3b0e308dc74279a303e17249c0bfa25`
- native-log SHA-256:
  `0cce4b9fd7155e8d5ef125026bcd39011027ebfac5fd2e8e3a55706be310b252`
- progress SHA-256:
  `6b5c9b6c4e4e7f93497a90518cec1e999c33796382c3ee6dae174f8d7f063034`

Do not retry or patch from the trailing method name alone. The next session
must begin with a bounded diagnostic that retains the crash IP/registers or an
equivalent exact MIR function/expression owner, then add a focused reproducer
before changing code. Stage 3, tools-only Stage 4, local deployment, rebase,
and push remain blocked.
