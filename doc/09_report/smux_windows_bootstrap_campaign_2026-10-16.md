# Windows smux compiler rebuild campaign

Source: immutable detached worktree `D:/dev/simple-smux-bootstrap-20261016`, commit `f612b3f68d6fc315b44df0cff8ec8a6f1db0f5da` (reviewed smux feature and MIR fix). Previous frozen source and producer evidence remain untouched.

Reason: prior exact Phase 2 producer emitted a caught LLVM codegen failure in `smux_pane_spawn_pty` from erroneous transfer-envelope lowering. That binary cannot contain the reviewed MIR owner/symbol fix. Rebuilding the compiler, then compiling smux with its actual bytes, is necessary. Rust is permitted only as the canonical bootstrap producer; application and test claims must use the resulting pure-Simple phases.

Finite dependency graph:

1. Canonical Stage 2 trust-root rebuild/admission, with canonical seed/runtime preparation and phase qualification.
2. Compile and execute real Hello with the exact new Phase 2 compiler; record compiler/output hashes and expected stdout/exit.
3. Phase 2 smux focused native build against the reviewed source; preserve source-qualified capsule caches and all actual failure diagnostics.
4. After actual Hello succeeds and canonical planner admission exists, enter the requested Stage 3 continuation. Repeat its own Hello compile/run before dependent application evidence. Compiler-only phases never stand in for a general SSpec/docgen runner.

Initial checked prerequisites: native Windows 11 Pro 10.0.26300 x64; Git Bash `C:/dev/tool/Git/bin/bash.exe`; LLVM prefix `/c/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc`. The canonical PATH-access fixture passed all ten cases (`build/smux-windows-bootstrap/path-fixture.stdout.log` in the new worktree). One backend job was selected, with normal canonical resource and admission checks retained. Rust authority generations and leases are owned by the canonical wrapper; none were copied from another session. No other-session source/cache was changed.

## Initial startup failure and supported correction

First invocation used the default centralized output. It exited before compilation: `VERDICT — ABORTED: stage=starting exit=1 signal=none reason=starting`, preceded by `materialize-symlinks-windows: receipt must use the dedicated bootstrap output root`. Logs: `build/smux-windows-bootstrap/campaign.stdout.log` and `campaign.stderr.log` in the new worktree.

Source inspection found an incompatibility: `scripts/bootstrap/lib/centralized-storage.shs` defaults output below `.simple/storage/build/bootstrap`, while `scripts/setup/materialize-symlinks-windows.shs:418` permits in-repository receipt paths only below `build/bootstrap/`. The documented absolute `--output` override selects an allowed dedicated descendant; bare `--output=build/bootstrap` would be remapped to the centralized default. No materializer or admission check is bypassed.

Corrected command, run from the immutable worktree:

```sh
bash scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --backend=llvm --mode=dynload --jobs=1 --keep-going --produce-stage3-receipt=verify-reviewed-compiler-fix --output=/d/dev/simple-smux-bootstrap-20261016/build/bootstrap/smux-campaign --progress
```

This is the documented receipt-free Stage 2 trust-root lane, followed by the canonical planner receipt producer bound to the admitted new parent. `--full-bootstrap --stop-after-stage3` is not receipt-free and is not used to circumvent that dependency.

Corrected campaign native parent PID: **756**; tool execution session: **79327**. At the first follow-up observation its Bash child PID 8680 was live and materialization had begun. Launch script and PID/status/stdout/stderr are retained in `D:/dev/simple-smux-bootstrap-20261016/build/smux-windows-bootstrap/` with the `campaign-attempt2` prefix. The owner monitors every 30 seconds and reaps the owned tree if its 7200-second outer campaign limit expires; canonical per-row checks remain enabled. No compiler, Hello, smux, Stage 3, or SSpec PASS is claimed while this campaign is running.
