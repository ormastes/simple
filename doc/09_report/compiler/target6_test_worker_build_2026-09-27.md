# Target 6 current-source test-worker build attempt (2026-09-27)

An isolated build used the admitted pure-Simple Stage2 compiler at
`/home/yoon/dev/simple/build/mini_builds/transient_name_owner/stage2-rebuild/admitted/simple`
(SHA-256 `319c7bd2f4dc15a0209fc0f76b805ff27afeecb4a411f8ad68c743191f0103d9`)
against this worktree's current `src/app/test_runner_new/main.spl` closure.
`SIMPLE_NO_STUB_FALLBACK=1` was set, and its cache was preserved at
`build/bootstrap/tool_cache/stage2/319c7bd2f4dc15a0/test-runner`.

- The default `core-c-bootstrap` lane reached linking, then failed on
  `rt_vulkan_*` and `rt_cuda_*` symbols in the runner's GPU imports. Its log is
  `build/mini_builds/target56_current_test_worker/build.log`.
- A `host-gpu` retry pointed at `src/compiler_rust/target/release`, which has
  `libsimple_runtime.rlib` but no `libspl_hosted_runtime-*.rlib`; discovery
  failed before linking. Its log is `build-host-gpu.log` in the same directory.
- The last `host-gpu` retry used a mistyped bootstrap-generation directory
  (`...4d2e...` instead of `...4d2d...`), so discovery again failed before
  linking. Its log is `build-host-gpu-authority.log` in the same directory.

The repository's `find_hosted_runtime_rlib` searches the selected runtime
root and its `deps` directory for `libspl_hosted_runtime-*.rlib`. Such an
archive existed under the main checkout's
`src/compiler_rust/target/bootstrap.generations/*/deps/` at the time of this
attempt, but no worker was produced. A later read-only lookup found the
candidate parent
`/home/yoon/dev/simple/src/compiler_rust/target/bootstrap.generations/e9bc8b090051808ec54c44144b026757495cbcd80b910374063123a70da180ec-18db7bef4d2d7e65160c2165d975a1034565fa83da622fc39f791639004c7e1f`
with `deps/libspl_hosted_runtime-818001c66b6e1b4b.rlib`. Its ABI match has
not been proved. The next isolated build should discover and pass the actual
parent of `deps` from a current archive, reuse the cache, then prove runner
results with a `Results:` line. The three-attempt session cap prevents another
retry here. No Target 6 spec has a current-source PASS.
