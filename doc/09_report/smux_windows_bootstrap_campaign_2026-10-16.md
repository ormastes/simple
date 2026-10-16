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

Follow-up live evidence: the corrected campaign passed Windows source materialization and native C admission (`bootstrap-windows-c-admission ... status=0`), found LLVM 23 shared provider `LLVM-C.dll`, and entered canonical Rust seed/runtime construction. At observation native Cargo PID 23188 and rustc PID 22772 were live; the canonical progress journal reported `milestone=rust-rust-seed-build`, `terminal=running`, eight tree processes and approximately 347 MB tree RSS. Authority staging root is `build/bootstrap/smux-campaign/rust-authority-75ad980a33be1ccc4bc84fa26d54327ff6b2124908a7ca0d17d835094312cdc3`. The campaign remains under the same native parent PID 756 / tool session 79327; these are live observations, not a compiler admission or completed seed claim. Continue observing the same owner; do not restart because a tool observation yields or expires.

## Prepared downstream Windows product composition

The editing checkout now contains additional native Windows providers and smux features that are intentionally absent from the active immutable f612 compiler snapshot. After the rebuilt pure-Simple producer qualifies, freeze those final product bytes in a separate checkout/commit and compile that source with ordered roots: **`src/providers/windows_native/lib` first**, then `src/os`, `src/lib`, and `src/app/hosted_apps`. The `lib` suffix is necessary: it is the root used by the source-selection contract. This selects the public `std.sys.pty` and synchronous `std.nogc_sync_mut.sosix.network` overlays while retaining original SFFI HTTP/UDP providers. Explicit root-order tests are authored; source review is not their execution.

Prepared argument shape (template; not yet executed): `<admitted-phase2-or-phase3-compiler> native-build --source src/providers/windows_native/lib --source src/os --source src/lib --source src/app/hosted_apps --entry-closure --entry src/app/hosted_apps/smux_client.spl --backend=llvm --runtime-path <matching-frozen-runtime-authority> --cache-dir <private-producer-and-product-cache> --output <private-smux-output>`. Bind the actual admitted compiler hash, product commit, source-root order, matching runtime bytes, toolchain and output/cache paths before launch. The Windows native linker owners already include `kernel32.lib` and `ws2_32.lib`; this is source evidence only and does not establish successful ConPTY/TCP linking or runtime behavior.

Consume the exact canonical Stage 2 Hello compile/run receipt if the campaign has already produced it successfully for these compiler bytes; do not repeat that unchanged green acceptance gate. If it has not, run the smallest real Hello compile and execute its resulting binary once, recording actual stdout and exit. Phase 3 may start provisionally only after that actual gate, and must separately acquire canonical admission before formal qualification. No Rust seed application tests and no general SSpec execution on compiler-only phases are permitted.

## Canonical Stage 2 construction reached

The same corrected campaign progressed to `Stage 2: admitted parent → bootstrap_main.spl`. Canonical Rust seed, native-all runtime, and compiler-backfill build logs each ended `native_process_status=0 shell_status=0`. The published Rust authority current marker records generation `75ad980a33be1ccc4bc84fa26d54327ff6b2124908a7ca0d17d835094312cdc3-669fe18cff33251319460c404e09fa42085092ceac7c2b5296fc1e02676f2240`, generation hash `669fe18cff33251319460c404e09fa42085092ceac7c2b5296fc1e02676f2240`, stamp hash `14957329744b6865862b5e21e31a4db813b395a597c4a964ee3a047409e35331`. Exact Rust seed SHA-256 is `9a9a921edf3d1675fc763aad9ff0adaac6be04358b889ff5d0e15e1b8c78a47e` (17,630,720 bytes). This identifies the bootstrap producer only; it is not an application/test runner substitution.

Actual Stage 2 native builder PID 23692 was live at campaign elapsed approximately 5066 seconds, CPU 2146 seconds, RSS approximately 616 MB. Its private staging `build/bootstrap/smux-campaign/stage3/x86_64-pc-windows-msvc/native-objects-yLqywb` contained 867 actual `.o` files totaling 21,447,104 bytes; latest `mod_866.o` was written at 11:11:14 local time. This demonstrates compiler construction progressing; the final Stage 2 executable and its Hello/admission gates were still pending. Observe the same owner/session, preserve this staging/cache, and do not restart solely because an observation handle yields.
