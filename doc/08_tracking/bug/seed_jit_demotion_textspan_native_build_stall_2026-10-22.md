# Bug: phase-1 seed JIT-demotes native_build_main.spl (native-build stalls) AND FileTextSession reads fail (file_read returns "")

Date: 2026-10-22
Lane: work/phase1-mcp-redeploy-20261021 (worktree on release_phase3 base 3b02fed6a0c); verification lane work/release10-smux-verify-20261022 (worktree on origin/release/1.0 e1607892a4f)
Host: DESKTOP-5A4V03J, Windows 10 / Git Bash, x86_64-pc-windows-gnu, 12 CPUs, 32 GiB RAM
Producer: phase-1 seed (Rust, nightly-2026-09-15, cranelift); also reproduced on the git-tracked `bin/simple.exe` seed

## Second defect: `file_read` returns "" — `external text byte buffer allocation failed`

Any spec that reads repo files through `std.io_runtime.file_read` /
`file_read_result` gets an empty string under the phase-1 seed AND under the
git-tracked `bin/simple.exe` seed (both fail identically on origin/release/1.0,
2026-10-22):

```
match file_read_result("test/01_unit/os/smux_spec.spl"):
    case Ok(c): ...
    case Err(e): expect(e).to_equal("")
# -> expected "external text at byte -1: external text byte buffer allocation failed" to equal ""
```

`file_exists` (rt_file_exists FFI) works; the failure is inside the
`FileTextSession.open/read` text path — the external-text byte buffer
allocation fails at byte offset -1. This makes every file-reading spec fail
vacuously:

- `test/03_system/tools/smux_caret_sspec_quality_system_spec.spl`: 7/14 on
  release/1.0 (all seven failures are empty-read artifacts: counts 0,
  `present`-via-classifier false; the mirror `file_exists` checks pass).
- `test/03_system/app/devhub/feature/devhub_multi_target_gateway_spec.spl`:
  3/14 ("persist one target ... expected 0 to equal 2" — read-back of the
  persisted config returns "").
- `test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl`: 7/10
  (checks `bin/simple.exe` output content).

Specs that do not read files through the text session are unaffected:
`smux_system_spec.spl` passes 56/56 on release/1.0.

Suspected root cause: seed external-text buffer allocation rejects the
session read (negative/unknown byte offset -1) — same family as the seed
memory-retention defect (bootstrap_stage2_seed_parent_retention_oom_2026-10-22.md).
Needs a `SIMPLE_JIT_STRICT=1` / native backtrace from `FileTextSession.read`.

Workaround: none for file-reading specs under the seed; run them on a
pure-Simple-built `bin/simple` once the pure-Simple binary is available.

## First defect: native-build stalls (original report)

## Symptom

Any `native-build` driven by the phase-1 seed starts, emits JIT-demotion
diagnostics for `src/app/cli/native_build_main.spl`, prints a workaround-store
lock failure, and then makes no further observable progress: no cache entries,
no object files, no log growth — while the seed process continues to burn CPU
for hours.

Two independent runs on 2026-10-22 (MCP/LSP/spipe rebuild via
`bootstrap-mcp-build-deploy.shs`, and a direct `native-build` of
`src/app/hosted_apps/smux_client.spl`) both stalled this way and were killed
after 6 h 44 m and 2 h 28 m respectively with zero artifacts produced.

## Evidence (2026-10-22, same lane, phase-1 seed)

1. **JIT demotion** (both runs' logs):
   ```
   [jit-fallback] HIR lowering error: Cannot infer field type: struct 'TextSpan' field 'end' (declared fields: value, start, len) [in src/app/cli/native_build_main.spl]: whole module dropped to the interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1 to turn this into a hard error.
   [engine-demotion] reason=jit-compile-error detail=HIR lowering error: Cannot infer field type: struct 'TextSpan' field 'end' (declared fields: value, start, len) [in src/app/cli/native_build_main.spl]
   [INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: ...
   ```
   The seed's HIR lowerer cannot infer the field type of `TextSpan.end` in
   `native_build_main.spl`. The module owning the native-build driver logic is
   the one demoted, so the driver itself runs interpreted.
2. **Workaround-store lock failure** (last line of both runs' logs):
   ```
   workarounds: refresh failed: workaround writer lock unavailable
   ```
   The MCP run — started 12:33 — already hit this at 12:35, before any other
   seed native-build existed, so the lock was either held by an earlier crashed
   run's stale lockfile or the lock acquisition has a defect (no lockfile was
   present under `var/lib/` at inspection time).
3. **Zero progress after demotion**:
   - MCP/LSP/spipe run: pid alive from 12:33 to 19:16 (~6 h 44 m, ~16,100 s CPU);
     cache dir (`build/bootstrap/mcp-native-cache`) stayed **0 bytes**; per-server
     build logs last written 12:34/12:35; no deployed artifacts.
   - smux client run: pid alive from 16:48 to 19:16 (~2 h 28 m);
     `build/bootstrap/smux-native-cache` was **never created**; log last written
     16:50; no `smux_client.exe` produced.
4. Interpreter fallback is documented by the seed itself at ~100-1000x
   slowdown; combined with the per-file driver work this makes completion
   impractical (extrapolated: days per entry-closure on this host).

## Impact

- **MCP/LSP/spipe native rebuild + redeploy from the phase-1 compiler is
  blocked.** The previously deployed binaries under `bin/release/` remain the
  old ones (deploy never ran).
- **smux client native build is blocked** (goal item 1 "build smux" cannot
  complete with the phase-1 compiler).
- **All file-reading system specs fail vacuously under the seed** (smux caret
  quality, devhub gateway/TUI); they cannot be used as verification evidence
  until the seed text-session defect is fixed.
- Any future bootstrap stage that routes `native_build_main.spl` through the
  seed JIT hits the same demotion.

These are seed (`src/compiler_rust`) defects, not Simple-source defects:
`TextSpan` in the Simple sources declares `value, start, len` and the seed HIR
lowerer fails on a field (`end`) the JIT frontend believes exists. The
workaround-lock failure is a second, independent seed-side issue.

## Suspected root causes

1. Seed JIT HIR frontend field inference desync for `TextSpan` (frontend
   expects an `end` field that the declared struct does not have — likely a
   span-type mirror in the JIT's own sources vs the Simple-side struct).
2. Workaround writer lock: either stale lockfile cleanup is missing on abnormal
   exit, or lock acquisition retries exhaust immediately; message gives no
   owner/path detail.

## Suggested next steps

1. Reproduce with `SIMPLE_JIT_STRICT=1` to fail fast and get a full HIR
   lowering backtrace for the `TextSpan.end` inference error.
2. In `src/compiler_rust`, align the JIT frontend's span-field expectation with
   the Simple-side `TextSpan` declaration (`value, start, len`), or add the
   missing field inference rule.
3. Make the workaround writer lock print holder pid/path and add stale-lock
   reaping after a TTL.
4. Until fixed, do not start long-running seed `native-build` jobs without a
   progress watchdog (cache-dir growth + log mtime); kill after ~30 min of
   zero progress.

## Workaround

None known for native-build via the phase-1 seed. Interpreter-mode
`simple test` / `simple check` work fine and are unaffected (specs pass; see
smux system specs 56/56 on this lane). Use the previously deployed
`bin/release` binaries for MCP/LSP until the seed JIT defect is fixed.
