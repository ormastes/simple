# Bootstrap --pure-simple stage2 stalls on yoon-note (7200s timeout, no binary)

Date: 2026-07-02
Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
Severity: P2
Related: doc/08_tracking/bug/jit_lowering_module_alias_and_panic_2026-07-02.md (needs redeploy to verify JIT)

## Symptom

`scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple` stage 2
(`target/bootstrap/simple native-build --backend cranelift --source
src/compiler --source src/app --source src/lib ...`) runs for the full
7200 s worker budget and is killed without producing a binary. The
hir-lower phase log ends at:

```
[hir-lower] bootstrap-functions:deferred
[hir-lower] bootstrap-functions:count 0
[TIMEOUT: Process killed after 7200s]
```

No further progress lines for 2 h — the worker appears wedged in/after
hir-lower rather than slowly progressing.

## Context

- Host cannot rebuild the Rust seed (`llvm-sys`: missing LLVM `Polly`
  static lib), so `--pure-simple` is the only rebuild path here.
- Also observed: `warning: failed to initialize runtime provider
  DynamicPath(.../target/bootstrap): Is a directory; falling back to static`.
- Consequence: the deployed `bin/release/x86_64-unknown-linux-gnu/simple`
  (which predates `rt_len` in the JIT runtime symbol table) cannot be
  refreshed on this host; every EngineColor/game2d program stays
  interpreter-only despite all HIR lowering blockers being fixed.

## Next steps

- Try the suggested alternatives: shrink `--source`, or the in-process
  backend; or rebuild + deploy from a host with a working LLVM dev setup.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
