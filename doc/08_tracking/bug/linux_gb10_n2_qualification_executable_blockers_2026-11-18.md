# Linux GB10 N2: no runnable qualification executable (seed native-build stall + interpreter "value is not callable")

- **Filed:** 2026-11-18
- **Status:** open (2 and 3 fixed; 1, 4 and 5 open)
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

### Root cause (diagnosed 2026-11-18): runner defect, not the interpreter

The reported line is misleading. Temporary `print` traces showed that
`_sha256_matches("/proc/self/exe", ...)` in `worker_engine2d` returns `true`.
The failure is in the same-named private helper in `scene_contract.spl`, which
`web_worker_scene` reaches. The interpreter reports the error against the
helper-name line in `main.spl`. Commit `24bd582e686` (the rewrite that made
`file_hash_sha256` return `text?`) produced this at `scene_contract.spl:209`:

```
not _sha256_matches(scene_reference_path(kind), scene_reference_sha)(kind)):
```

That passes the function `scene_reference_sha` as the digest, then calls the
returned `bool` with `(kind)`, so "value is not callable" is a correct
diagnosis. The fix is `scene_reference_sha(kind))`. No other line in that
commit has the same shape. The following all passed under the seed:

- minimal repros of the `if val` pattern;
- a private helper duplicated across modules;
- the `getpid` JIT demotion.

The `getpid` ambiguity only demotes the JIT to the interpreter and is
unrelated.

Red/green evidence: a new `it` in
`test/03_system/app/ui/feature/corpus_case01_physical_capture_spec.spl`
calls `web_worker_scene(SCENE_CORPUS_CASE01)`. Before the fix it fails with
`value is not callable`. After the fix it gets past the digest checks and then
fails on Blocker 3, which is independent. Logs:
`/home/yoon/skia-n2/artifacts/spec_red.log` and `spec_green.log`.

## Blocker 3 — case 01 Web admission rejects `background-position-x`

With the runner fixed, the case 01 Engine2D worker still fails under the seed
interpreter. The command is `worker-engine2d-corpus-case01`, with the same
argument shape as above. It now exits with:

```
status=blocked reason=web-admission:unhandled-paint-style-value:1:background-position-x
```

The same reason also fails the two existing `it`s in
`corpus_case01_physical_capture_spec.spl`, so the problem is not specific to
the runner. `01-solid-boxes.html` sets no `background-position`, which means
the layout producer (`simple_web_html_layout_renderer_paint_draw_ir.spl:193`)
emits command 1 with a non-`0` `background-position-x`. (The first diagnosis
was that the producer was wrong. That was corrected the same day; see the root
cause below.) Log:
`/home/yoon/skia-n2/artifacts/seed_worker_engine2d_case01_after_fix.log`.
No readback was obtained, so cases 06 and 02 were not run.

### Blocker 3 root cause (fixed 2026-11-18): the admission reader, not the engine

The engine is right. CSS initial `background-position` is `0% 0%`. The
producer encodes percentages as `-1000 - pct` (`_background_position_value`,
`simple_web_html_layout_renderer_declarations.spl:325`), and the `background`
shorthand resets the longhands to that initial value: `-1000`, in
`simple_web_html_layout_renderer_decl_apply.spl:367`. `_web_style_neutral`
accepted only `"0"`, so it misread the 0% encoding as an offset. Any Web
fixture that uses the shorthand was rejected, including the pinned
`web_opaque_box_v1.html`.

The fix accepts exactly `"0"` and `"-1000"`. Center (`-1050`) and every other
offset are still rejected; a new `it` in `web_opaque_box_stage1_spec.spl` pins
both cases. Red on base: 5 `it`s across `web_opaque_box_stage1_spec` and
`corpus_case01_physical_capture_spec` fail with this reason. Green on head:
5/5 and 4/4.

## Blocker 4 — Engine2D strict capture producer half lost in merge `e5b290e42a0`

With admission fixed, the case 01 Engine2D worker on the GB10 gets further.
`vkCreateDevice` returned `VK_ERROR_INITIALIZATION_FAILED` 4 times and then
succeeded on attempt 5. The worker then fails:

```
error: semantic: src/app/test/vulkan_2d_qualification/main.spl:2258:17: class `Engine2dDrawIrAdvSubmitResult` has no field named `submission_generation`
```

`main.spl` has 864 lines. The real site is
`src/lib/gc_async_mut/gpu/engine2d/final_output_capture.spl`
(`engine2d_strict_vulkan_capture_completed_submission`), which reads
`submission.submission_generation` and `result.submission_generation`. This is
the second case of the interpreter reporting the wrong file and line.

Neither `Engine2dDrawIrAdvSubmitResult` nor `Engine2dDrawIrAdvResult`
(`draw_ir_adv.spl`) has `submission_generation`, and the result struct also
lacks `frame_width` and `frame_height`. This holds on `release/1.0.0` and on
`origin/main`. Those fields, and the strict-Vulkan producer code that sets
them, were added by wip commit `ef35100f1d4` (2026-09-24).

Merge `e5b290e42a0` ("converge session fixes onto origin/release_phase3",
2026-10-22) took the consumers from that commit: `final_output_capture.spl`,
the `*_capture_artifact.spl` files, and `final_output_capture_spec.spl` and
`physical_capture_artifact_spec.spl`, which construct both structs with those
fields. It kept parent 1's `draw_ir_adv.spl`, which has none of them. Parent
`8484154793` has 0 occurrences of `submission_generation: i64 = 0`; parent
`ef35100f1d4` has 2.

Measured on head: 227 of the 344 non-trivial lines that the wip added to
`draw_ir_adv.spl` are absent. That includes the fractional and affine
strict-Vulkan pixel helpers. `Engine2D.latest_vulkan_frame_receipt()` and
`vulkan_submission_generation()` do exist (`engine.spl:4598`, `:2330`).

Not restored here. It is a 3-week-stale lost-half backport into a hot file,
and it needs its own lane and review. Log:
`/home/yoon/skia-n2/artifacts/w-engine2d-corpus-case01.log`.

## Blocker 5 — seed interpreter has no `rt_gpu_provider_loaded`

The case 01 Skia worker, under the seed interpreter on the GB10 with the
provider env set, fails with:

```
error: semantic: unknown extern function: rt_gpu_provider_loaded
```

The symbol is declared in `src/lib/nogc_sync_mut/gpu/provider.spl:8`. Its
backing exists in `src/runtime/runtime_dynload.c:1477` and in the seed's
`runtime/src/gpu_provider_twins.rs`, but the seed interpreter's extern dispatch
does not register it. This is a seed gap and is not patched here. The Skia leg
therefore needs the native executable (Blocker 1). Log:
`/home/yoon/skia-n2/artifacts/w-skia-corpus-case01.log`.

No readback was obtained on either leg, so cases 06 and 02 were not run.

## Not done here

Blockers 2 (runner) and 3 (admission reader) are fixed. Blockers 1, 4 and 5
are open. A pure-Simple self-hosted aarch64 release binary would bypass
Blockers 1 and 5, but not Blocker 4. The interpreter error
and the `getpid` ambiguity are defects in their own right.
