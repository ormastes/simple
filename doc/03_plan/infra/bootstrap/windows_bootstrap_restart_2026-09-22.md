# Windows bootstrap restart — 2026-09-22

## State at handoff

- The Windows bootstrap is **stopped**. No bootstrap or sampler process remains active.
- Stage 2, Phase 2 binary tests, and Stage 3 have **not** passed on this candidate.
- Base `e0dd873da1b7828389db4eb60e82972cc8245313` first stopped on an
  uninitialized `.spipe/spipe` gitlink, then an unexpected Git batch EOF.
- Reviewed fixes on draft Simple PR #1265 are `25e4d785681` (initialize the
  recorded gitlink), `41ecbed73f0` (bounded Git child diagnostics), and
  `d0ef8db87ad` (receipt directory handle access). The last D: replay reached
  junction creation but failed `api.set-junction-tag:win32=5` before Stage 2.
- Follow-up commit `2984a5ff9bda30979c5853068681bb6765f7cc19` restores
  write access **only** for junction creation. Its focused regression passes on
  C: NTFS and D: ReFS, including receipt rename and target safety checks.
  **Full bootstrap on this exact commit remains pending.**
- SPipe remains pinned to recorded gitlink `155d58a4898750bf9e20f8f1d656ad8185111687`.
  Do not move it to divergent Spipe `main` during this replay.

Evidence is retained at `D:/wk-bootstrap-receipt-d0ef8db/.simple/` and
`C:/Users/ormas/dev/simple-replay-materializer-combined/.simple/`. The partial
`C:/Users/ormas/dev/b-d0ef` checkout stopped at 21%; do not treat it as clean
or reuse its incomplete source tree. The previous aggregate RSS sample peaked
at 249,716,736 bytes but predates compiler execution.

## Restart sequence

1. Start from a **fresh, clean, short-path Windows worktree** at the exact
   reviewed head containing `2984a5ff`; verify its SHA and the recorded SPipe
   gitlink. Initialize that exact submodule commit without `--remote`.
2. Verify LLVM 23.1.1 `clang-cl.exe` from
   `C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin`, MSVC target and
   linker flavor, and C compilation mode (`CL=/TC`). Preserve the seed's own
   LLVM binding setup while pinning the native C compiler to LLVM 23.1.1.
3. Run one bounded Windows bootstrap with a private output/cache root and
   `SIMPLE_NO_STUB_FALLBACK=1`:

   ```sh
   source scripts/setup/windows-msvc-bootstrap-env.shs
   export CC='C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin/clang-cl.exe'
   export CXX="$CC" CL=/TC SIMPLE_LINKER_FLAVOR=msvc
   export SIMPLE_LLVM_BIN='C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin'
   sh scripts/bootstrap/bootstrap-windows.sh --msvc --full-bootstrap \
     --stop-after-stage2 --backend=llvm --mode=dynload --jobs=12 \
     --output=build/bootstrap-restart-2984 --progress=build/bootstrap-restart-2984/progress.log
   ```

4. Record the exact HEAD, command, terminal exit, materializer receipt, Stage 2
   admission hash/capsule, elapsed time, and sampled process-tree CPU/RSS.
   Materializer success alone is not Stage 2 admission. If the Git batch exits,
   use its bounded child stderr/exit diagnostics and stop at that actual cause.
5. Only after Stage 2 admission, build the non-vacuous full CLI and test runner
   in phase-bound caches. Run the supported Phase 2 interpreter, compiler, and
   loader binary tests. Require executed counts and a final `Results:` verdict;
   exit zero alone is insufficient. Do not silently substitute the Rust seed.
6. Start Stage 3 only after the Phase 2 gate passes and its parent admission
   receipt, candidate path, ABI policy, and hashes agree. Record Stage 3 build
   and whole-test receipts separately. Keep Stage 4 on hold until Stage 3 passes.

## Stop rule

The next session gets at most three verify/fix cycles for each new failure.
Do not repeat a passing check or launch a duplicate full bootstrap against the
same head and conditions. On failure, preserve the log and exact command, add
a focused reproducer and bug record, and stop the dependent phases. Do not
claim bootstrap success or promote PR #1265 from draft until exact-head
admission and required tests pass.
