# Linux GB10 N2: no runnable qualification executable (seed native-build stall + interpreter "value is not callable")

- **Filed:** 2026-11-18
- **Status:** open, not attempted (filed only)
- **Blocks:** `doc/08_tracking/todo/simple_2d_skia_renderdoc_linux_n2_2026-09-27.md`
  (cases 01/06/02 on the NVIDIA GB10 have no worker readbacks)
- **Host:** physical aarch64 Ubuntu 24.04.4 LTS, NVIDIA GB10. There is no
  self-hosted pure-Simple release binary on this host (`bin/release/` absent).
- **Binary:** the blend seed `/home/yoon/.cache/cargo-target-webrender-blend/release/simple`,
  sha256 `119feb0f865390b5dabb084e8b3ec94a4e5dbb391ffae2339b9af6fc7bd01b91`.
  It prints the "bootstrap seed only" banner, and it passes a failing-assertion
  control (`expect(1).to_equal(2)` exits 1).

## Blocker 1 — seed `native-build` produced no qualification binary in 2 h

Exact command: the README recipe, run from the worktree root at release/1.0.0
`9368a4df112`.

```sh
systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 \
  /usr/bin/time -f '%e s %M KB' timeout 5400 \
  /home/yoon/.cache/cargo-target-webrender-blend/release/simple native-build \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/test/vulkan_2d_qualification/main.spl \
  --strip --output build/optional/vulkan_2d_qualification
```

Observed (no error text was ever printed — the failure is the absence of output):

- 0–65 min: one thread at ~98 % CPU, RSS ~2.5–2.6 GB, `write_bytes` flat at
  20.6 MB. The log stopped after the load-time warnings (`[visibility-warning]`,
  `[gc-warning]`, the `W-STR-BRACE-001` lines) and the closing
  `workarounds: incomplete coverage; run simple check-dbs --fullscan bugs`.
- About 65 min in, the driver spawned
  `simple run src/app/cli/native_build_worker.spl --source src/compiler …`.
  That interpreted child was still at 100 % CPU 58 min later, with RSS growing
  from 2.5 to 4.1 GB.
- At about 2 h 04 min there was still no `build/optional/vulkan_2d_qualification`.
  (The outer `timeout` was removed at about 65 min so the run could continue.)
  The run ended when its worktree was deleted, not by its own exit.

A variant without `--source src/compiler`
(`SIMPLE_NATIVE_BUILD_TRACE=1 SIMPLE_CACHE_SCOPE=n2-hedge`, `MemoryMax=6G`) was
OOM-killed by its scope 29 s after starting (journal: `run-r629430b4….scope: A
process of this unit has been killed by the OOM killer`).

What is unknown: whether the build would finish given more time, and where
the time goes. The seed runs the build as an interpreted Simple driver, and no
trace output appeared before the cutoff.

## Blocker 2 — interpreter rejects the runner: `main.spl:67:9 value is not callable`

This is the fallback of running a worker in-process under the seed, which
could only ever give candidate-grade (non-PASS) pixels. Exact command, from the
worktree root at release/1.0.0 `0d4cd599298`:

```sh
VK_DRIVER_FILES=/usr/share/vulkan/icd.d/nvidia_icd.json \
/home/yoon/.cache/cargo-target-webrender-blend/release/simple run \
  src/app/test/vulkan_2d_qualification/main.spl worker-skia-corpus-case01 \
  build/test-artifacts/vulkan_2d/n2-seed-case01-skia \
  /home/yoon/.cache/cargo-target-webrender-blend/release/simple \
  /home/yoon/skia-n2/artifacts/libsimple_upstream_skia_ganesh_vulkan.so \
  758f717f521fe4e996f41170a0cd70b53492c94df92d01d570f45f262605bc89 <64-hex nonce>
```

Exit 1. The JIT is demoted first, then the interpreter fails semantically:

```
[jit-fallback] HIR lowering error: ambiguous call to `getpid`: 2 co-compiled definitions (src/lib/nogc_sync_mut/io/sysinfo_ops.spl, src/lib/nogc_sync_mut/io_runtime.spl) and `src/lib/nogc_sync_mut/io/linux_machine_process_origin_v1.spl` neither defines nor imports it, so no definition can be selected. ... [compiler_cross_module_private_symbol_collision]
error: semantic: src/app/test/vulkan_2d_qualification/main.spl:67:9: value is not callable
```

`main.spl:67` is the body of `_sha256_matches`:

```
fn _sha256_matches(path: text, expected: text) -> bool:
    if val actual = file_hash_sha256(path):
```

Log (reproduced twice, 2026-11-18): `/home/yoon/skia-n2/artifacts/seed_worker_case01.log`.

## Not done here

No fix was attempted, per the lane scope. A pure-Simple self-hosted aarch64
release binary would bypass both blockers for the N2 run. The interpreter error
and the `getpid` ambiguity are defects in their own right.
