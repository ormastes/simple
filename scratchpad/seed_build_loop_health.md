# Seed build loop health check (2026-07-12 ~23:44 UTC)

## Active processes
- PID 4126724: `cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p simple-driver --features llvm`
  - cwd: `/tmp/simpleos-gpu-clean` (a separate worktree/clone, NOT the main repo)
  - parent PID 4121375: `sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --fresh-cache --no-mcp --jobs=half`
  - grandparent chain: codex session (`codex resume 019f4ecf-...--yolo`) running in a tmux pane, PID 3033699 (elapsed ~15.3h — long-lived session, presumably re-invoking the script each pass)
  - `bootstrap-from-scratch.sh` itself has NO internal while/retry loop — it is a single linear pipeline (seed build → native-all → stage2 → stage3 → stage4). The looping is done by the outer agent/session re-invoking the whole script with `--fresh-cache` each time.
- PID 4133154: `cargo build --release -p simple-driver --bin simple -q` in the main repo (`/home/ormastes/dev/pub/simple/src/compiler_rust`), parent = a different codex session (3031436) also running the MCP/LSP servers. This one finished during observation (process gone by second check) — a short, one-off rebuild, not the continuous loop.

## Progress signal (via stdout/stderr redirected to logs)
fd 1/2 of PID 4121375 point to `/tmp/simpleos-gpu-clean/build/bootstrap/logs/x86_64-unknown-linux-gnu/rust-seed-build.log`, actively growing (mtime = now, 23:43:51).

Log tail (last ~40 lines): only rustc warnings (redeclared FFI signatures, unused `last_value` assignment) — **0 `error[`/`error:` matches**. Currently at `Compiling simple-driver v1.0.0-beta` — the final crate before `Finished`.

Sibling stage logs in the same dir, all from **this same iteration** (recent, ~23:33–23:43):
- `rust-native-all-build.log` — **0 errors**, ends `Finished \`bootstrap\` profile [optimized] target(s) in 4m 09s` → simple-native-all built successfully.
- `stage2-native-build.log` — 1 grep hit but it's a benign `warning: failed to initialize runtime provider ... falling back to static` (not a real error); log shows normal llc/mir-lower progress.
- `stage3-native-build.log` — **0 errors**, ends `Build complete: 1 compiled, 0 cached, 0 failed` / `Linked: build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple (115140 KB) via clang++`.
- `stage4-native-build.log` — stale from **this morning** (08:36, ~15h old), NOT touched by the current iteration yet. Its old content shows a real historical failure: `undefined reference to 'rt_process_run_timeout'` / `rt_is_none'` — a link error in the core-c-bootstrap lane needing `--runtime-bundle rust-hosted`. This is a known/pre-existing stage4 blocker, not evidence the current loop is failing (current pass hasn't reached stage4 again yet).

## Artifact freshness
- `/tmp/simpleos-gpu-clean/src/compiler_rust/target/bootstrap/simple`: 144 MB, mtime 23:28:52 (just now) — actively being rebuilt/replaced by this iteration.
- `/tmp/simpleos-gpu-clean/.../libsimple_native_all.a`: mtime 23:33:03 (just now).
- Main repo `src/compiler_rust/target/bootstrap/simple`: mtime **06:55:57** (~17h stale) — the main repo's own bootstrap dir is not the one being iterated by this loop.
- Main repo `target/release/simple`: mtime 23:36:58 (fresh, from the short separate 4133154 build).
- **Deployed `bin/release/x86_64-unknown-linux-gnu/simple`: mtime 2026-07-11 08:52** — ~39 hours stale. Nothing from either build has been deployed there during this observation window.

## Conclusion
The loop in `/tmp/simpleos-gpu-clean` is **SUCCEEDING per-stage** on this pass (seed compiles cleanly, native-all finished, stage2/stage3 linked with 0 errors) and is currently mid-way through re-compiling the seed again (driven by an outer agent re-running `--fresh-cache` repeatedly, not a script-internal loop). It has not reached stage4 in this pass; the last stage4 attempt (this morning) hit a real linker error needing `--runtime-bundle rust-hosted`, so if the pipeline reaches stage4 again unmodified it would likely reproduce that same undefined-symbol failure. No fresh seed has been deployed to `bin/release/x86_64-unknown-linux-gnu/simple` (still 39h stale) — so redeploy is not yet happening regardless of build success.
