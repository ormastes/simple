# Bootstrap --pure-simple stage2 stalls on yoon-note (7200s timeout, no binary)

Date: 2026-07-02
Status: open (blocks redeploying bin/simple on this host)
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

## Triage 2026-11-25 (fleet lane p2w1-ac, Windows worktree @ origin/release/1.0.0)

SKIP — needs a full `--pure-simple` bootstrap, which is out of scope and
prohibited in this lane (no seed/bootstrap builds on this host; the tracked
`bin/simple.exe` is used as-is). The record is also host-specific
(yoon-note, x86_64-linux, July 2026) and predates months of bootstrap-lane
work, so its "blocks redeploying bin/simple on this host" framing may no
longer describe any current host — but confirming that requires running the
very bootstrap this lane cannot run. Status left as filed; the next agent
with a working bootstrap host should re-run
`scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple` once and either
close this or re-file with current timings. No code change made.
