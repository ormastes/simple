# Whole-suite sweep final report (shard3, 2026-09-19/20)

Lane: `suite-2026-09-18` (Windows, seed runner `bin/simple.exe` built
2026-09-17, `--mode=interpreter`). PR #1106.

## Coverage

5,259 spec files swept in 16 parallel shards + tail shards (runner v2/v3:
per-spec timeout, whole-tree reap; v3 fixes a `wait $pid` hang after failed
taskkill that silently killed the first 16 shards near completion).
Every file has a verdict: PASS, FAIL, or hang-class (os_tls_system,
shared_multilingual_gpu_fonts_perf hang past 240s on the seed).

## Fail classification (1,624+ unique FAIL files, buckets not disjoint)

1. **Seed test-mode child-spawn neutering — ~546 specs.** `rt_process_run`
   returns (code=-1, "", "") for EVERY child spawn under
   `test --mode=interpreter` on Windows; identical probes work under
   `run`. Root-causes the entire `*_log_modes` cluster (~100), most scv_*
   app specs, check-zone child-process specs. Root cause and evidence:
   `doc/08_tracking/bug/posix_spawn_and_seed_process_debt_2026-09-19.md`
   (addendum). Not fixable in-lane: the seed binary is shared build output
   of other lanes and the project direction is replacement by the
   pure-Simple binary, not seed patches. Fix direction: pure-Simple test
   runner must wire `rt_process_run` in test mode at parity with run mode.
2. **Environment/hardware-gated — several hundred.** t32_hw (~72, needs
   TRACE32), rv*/hardware (~29, needs cross toolchains/QEMU), qemu/
   simpleos/baremetal (~72), editor/gui rendering (SDL/display), live
   adapters (minio). Windows POSIX-shell fixtures (`/bin/sh` heredocs,
   extensionless stubs) are also in this class.
3. **Stale spec pins (FIXED in this lane).** Largest single class fixed:
   wave-6 generated twins pinning `.? == true/false` on the `T?`
   passthrough operator (52 system + 63 unit/auto_comprehensive +
   type_inference + ffi/semihosting twins = 116+ specs). Also:
   `check/2`→`check_msg/2` merge-revert (stats_command), file-size 6→5
   byte-exact pin, empty-string presence pin, fn_lambda write-back pin,
   `.reversed()` pin, `val`→`var` accumulator, `@di_test` tag,
   `__enter__/__exit__` protocol pin, with_statement/memory_system/
   ffi_system seed-debt notes per ledger.
4. **Real tree bugs (FIXED in this lane).**
   - scv: `arr[i].field = value` complex-indexed-receiver restructures
     (event_coalesce, bulk_update, editor_ipc, warm_status) + Windows
     separator normalization (`scv_rel_path`, fswatch ignore matching,
     scv_should_skip) — greened ~15 scv specs both zones.
   - `module_loader_resolve`: `\`→`/` path join, cross-caller cache
     conflation, ambiguous cache key.
   - `di`: `resolve_or`/`get_extension` widened to `Any?`
     (non-optional-nil sweep missed sites).
   - `interpreter_load_facade_v1`: missing IL1 module authored against
     real shared authority modules.
5. **Spec-pinned never-implemented APIs — ledgered.**
   `doc/08_tracking/bug/spec_pinned_unimplemented_apis_2026-09-19.md`
   (11 surfaces incl. dbfs artifact_publication; need feature lanes or
   spec-retirement decisions).
6. **Seed interpreter/JIT divergences — ledgered singles** (error_path
   family, option-chain, dict identity, enum payload, core-interpreter
   alias split, `with` exit mutation, etc. — see doc/08_tracking/bug/).

## Perf question (user: "why is interpreter/JIT slow, par slower than before")

Answered in
`doc/08_tracking/bug/seed_test_preamble_cost_and_child_process_leak_2026-09-19.md`:
no measured JIT regression; the acute slowness was a child-process leak
(hundreds of hung `gen-lean verify` grandchildren accumulating on the
host). Fixed in-lane with tree-reaping runner v2 and
`sweep-windows-test-leaks.ps1`. Structural: `.simple_cache/` stays empty
in test mode so every spec re-JITs its preamble (~12s lib / ~90-100s
compiler-harness fixed cost per spec on the seed).

## Pure-Simple binary status

Blocked by the documented HIR-tail memory accumulation wall; not
attempted in this lane. The seed runner was the settled substitute per
the lane charter.
