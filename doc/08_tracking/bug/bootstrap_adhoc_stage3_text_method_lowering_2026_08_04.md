# Ad-hoc bootstrap tool blocked by Stage3 text/array MIR method lowering

## Status

Open. The detached worktree implementation reaches MIR with the verified
pure-Simple Stage3 producer but does not emit the local tool executable.

## Reproduction

Build `src/app/bootstrap_adhoc/main.spl` as a positional, entry-closure,
one-binary native build with `SIMPLE_NO_STUB_FALLBACK=1` and the verified
Stage3 compiler.

## Observed

The third and final bounded attempt fails closed with unresolved MIR method
calls including `join`, `substring`, `rfind`, and `slice`, followed by
unsupported enum MIR type kinds. The first two attempts exposed and removed a
broad `app.io`/`std.io` closure that incorrectly pulled `Future<T>` into the
small tool; the third attempt uses only bootstrap-safe synchronous facades.

Retained evidence:

- `build/bootstrap-adhoc-local/tool-build.log`
- `build/bootstrap-adhoc-local/tool-build-cycle2.log`
- `build/bootstrap-adhoc-local/tool-build-cycle3.log`

## Impact

No `build/bootstrap-adhoc-local/bootstrap-adhoc` executable exists, so the
worktree-local mode is not deployed and must not be offered to other sessions
yet. No main branch, shared `bin/simple`, or active Stage4 output was changed.

## Next bounded continuation

Use a fresh scoped session to replace unsupported convenience methods with
bootstrap-proven primitive loops, or fix the MIR receiver-method owner and add
native positive/negative coverage. Then build once, run `selftest`, run the
frontend positive/negative capsule, and inspect the non-release receipt.

## Fresh continuation evidence

A fresh three-cycle continuation replaced the broad I/O facade with the
dedicated `app.io.bootstrap_adhoc_ops` owner and removed every `join`,
`substring`, `rfind`, `slice`, and `merge` call from the capsule closure.
Stage3 still terminates with SIGSEGV during MIR lowering:

1. cycle 1 stopped immediately after text `replace` lowering;
2. cycle 2 stopped immediately after `split`/`trim` lowering;
3. cycle 3 stopped immediately after `contains` lowering.

Logs are retained as `tool-build-continuation1.log` through
`tool-build-continuation3.log`. The parallel exact Stage4 run also exited 1
without producing a replacement full compiler, so no newer admissible producer
is available in this workspace. Do not retry the same Stage3 binary; resume
only after its MIR receiver-method crash is fixed or a newer verified producer
exists.
