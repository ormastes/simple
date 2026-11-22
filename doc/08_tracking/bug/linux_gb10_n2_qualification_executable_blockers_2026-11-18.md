# Linux GB10 N2: no runnable qualification executable (seed native-build stall + interpreter "value is not callable")

- **Filed:** 2026-11-18
- **Status:** open (2, 3, 4 and 7 fixed; 1 diagnosed with a workaround; 8 and 9 open; 5 and 6 are interpreter-only — see the 2026-11-22 section)
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

### Blocker 1 — retry with `SIMPLE_BOOTSTRAP=1` (2026-11-18, release `cef56f64375`)

Same recipe, run from a detached worktree at `cef56f64375` (which includes
#10131), with the output under `/home/yoon/skia-n2/artifacts/nb_try/`:

```sh
SIMPLE_BOOTSTRAP=1 SIMPLE_CACHE_SCOPE=n2-nb-try \
systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 \
  -E SIMPLE_BOOTSTRAP=1 -E SIMPLE_CACHE_SCOPE=n2-nb-try \
  /usr/bin/time -f '%e s %M KB' timeout 10800 \
  /home/yoon/.cache/cargo-target-webrender-blend/release/simple native-build \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/test/vulkan_2d_qualification/main.spl \
  --strip --output /home/yoon/skia-n2/artifacts/nb_try/vulkan_2d_qualification
```

Timeline. Wall times are host clock; worker times come from the worker's own
`[build] ... elapsed_ms` lines:

| span | wall | measured |
|---|---|---|
| driver front end (single thread, ~98 % CPU, RSS ~2.5 GB, log silent after load warnings) | 05:29:50 → ~06:29:30 | ~60 min |
| worker `source_closure`, 506 files | from ~06:29:30 | 40.6 s |
| worker `load_sources` | | ends at 93.5 s |
| worker `parse`, 506 files | → 07:59 | 85.8 min (~10.2 s/file); worker RSS ~3.1 GB |
| worker `surface_build` | 07:59 → 08:16:35 | 76 of 506 files in ~17 min (~13 s/file) |
| remaining phases (task 2 of 6 onward) | not reached | — |

The outer `timeout` was removed at 08:00:17, on instruction, so the run could
continue past 3 h while it kept advancing phases. Its rc 137 is the removal,
not a build result. The run was then stopped at 08:16:35 by the disk guard
(`STOP disk below 4 GB, avail_kb=3664704`). That drop was caused by other
sessions: this build's own footprint was 338 MB of worktree `build/` and
1.7 MB of artifacts, and free disk kept falling to 3.0 GB after the stop.
**No binary was produced.**

What `SIMPLE_BOOTSTRAP=1` changed: unknown, and not attributable. This run
printed per-phase worker progress and spawned the worker at ~60 min (the
earlier run spawned it at ~65 min and printed nothing), but the release head
also moved between the two runs. At the measured rates, `surface_build` alone
would need ~95 more minutes, with four more phases after it, so a complete
build is plausibly longer than 6 h on this host. That throughput, ~10–13 s
per file in the interpreted worker, is the measurable target for Blocker 1.
Caveat for any future binary: under `SIMPLE_BOOTSTRAP=1` the seed weak-stubs
undefined `rt_*` symbols (`pipeline/native_project/stubs.rs:1101`), so a
capture extern could become a silent stub. Check a resulting binary's case
results against the fail-closed identity and receipt gates before using them.

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

### Blocker 4 — the readers' half is restored (2026-11-18, own lane)

The rewind is confirmed. `git log -S submission_generation` shows that no
later commit removed or replaced the producer on purpose; the only other hits
are history of `engine.spl` accessors. Merge `e5b290e42a0` dropped two things
that the release readers need:
- `draw_ir_adv.spl`: the strict submit/readback `submission_generation`
  producer, plus `frame_width`/`frame_height`;
- `engine.spl`: the `Engine2D.vulkan_device_type()` accessor.

Only these were restored. `final_output_capture_spec` went from 0/7 on base to
8/8, and `physical_capture_artifact_spec` from 0/1 to 1/1. `draw_ir_adv_spec`
is 68/70 on both base and head.

**Still lost from the same merge, and not restored** (no release reader of
`submission_generation` needs them): the fractional and affine strict-Vulkan
pixel helpers. With the field restored, `strict_vulkan_fractional_rect_spec`
(0/2) and `strict_vulkan_affine_coverage_spec` (0/3) now fail on
`fractional-geometry-unsupported` rather than the missing field. Case 02
(fractional edges) will need that hunk.

### Blocker 4 — the fractional and affine wiring is restored (2026-11-18, own lane)

A per-symbol `git log -S` proof showed the drop was accidental: every helper
occurs 0 times in parent 1, more than 0 in parent 2 and 0 on release.
`814795e109d`, which added the generic `fractional-geometry-unsupported`
preflight, is on parent 1's lineage and never saw the wip, so it was a
fail-closed default, not a reversal. The affine SPIR-V module and its shader
had landed; only the wiring was lost. Restored:

- the fractional pixel-center coverage rect;
- the session pipeline, the backend dispatch, the 60-byte push-constant pack
  and the Engine2D entry points for affine coverage;
- the strict preflight and executor branches.

Left out: fresh-device v4, the batch/composition v4 helpers and the image
damage hunks.

`strict_vulkan_fractional_rect_spec` went from 0/2 to 2/2 and
`strict_vulkan_affine_coverage_spec` from 0/3 to 3/3, on both lavapipe and
the GB10. The other strict and legacy specs give the same result on base and
head.

Case 01 Engine2D retried on the GB10 under the seed interpreter.
`vkCreateDevice` succeeded on attempt 4. Strict submit, the generation-linked
readback and the frame-receipt checks all passed. It then exited 3 with:

```
status=blocked reason=engine2d-capture:selected Vulkan physical device identity unavailable
```

That is Blocker 6.

## Blocker 6 — the seed interpreter cannot attest the Vulkan device UUIDs (by design)

The seed interpreter's `rt_vulkan_selected_device_identity_v1`
(`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:4442`) returns `""`
on purpose. In its own words: "It cannot attest that native Engine2D
framebuffer generation, so the typed Simple facade must reject this lane."
`vulkan_sffi_selected_device_identity_v1` therefore fails closed.

This is correct behaviour, not a defect. A physical N2 Engine2D capture can
only come from the native qualification executable (Blocker 1), the same as
the Skia leg (Blocker 5). Log:
`/home/yoon/skia-n2/artifacts/w-engine2d-corpus-case01-subgen.log`.

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

Blockers 2 (runner), 3 (admission reader) and 4 (the `submission_generation`
producer and the fractional and affine wiring) are fixed. Blockers 1 and 5 are
open; Blocker 6 is by design. A native
qualification executable is now the single gate for both case 01 legs. The interpreter error
and the `getpid` ambiguity are defects in their own right.

## 2026-11-22 — Blocker 1 root cause, first native executable, Skia leg green

Release `6b508da8f57`, same blend seed. Worktree branch
`work/webrender-native-skia-renderdoc-20261122`.

### Blocker 1 root cause: the stall was the interpreted driver, not the build

`simple native-build` on the seed dispatches to the pure-Simple driver
(`src/app/cli/native_build_main.spl`, interpreted). That is the 60 min front end
and the ~10 s/file worker. The seed's Rust handler is selected by
`SIMPLE_NATIVE_BUILD_RUST=1` (`driver/src/main.rs`, `native_build_rust_override`).
Same recipe plus that variable: `compiled=506`, 29.95 s wall, 1.49 GB RSS cold;
7–10 s warm. Blocker 1 as filed (throughput) is a defect of the interpreted
driver and stays open as such; it no longer blocks this lane.

### Blocker 7 (fixed) — `gpu_provider_device_identity` lost in merge `e5b290e42a0`

With the Rust handler, 505 of 506 files compiled. The one failure:

```
src/lib/skia/backend/upstream_ganesh_vulkan/provider.spl: hir: Unsupported feature: cannot infer field type while lowering _upstream_skia_render_admitted: struct 'ANY' field 'valid'
```

`provider.spl` imports `gpu_provider_device_identity` from
`std.nogc_sync_mut.gpu.provider`, which did not define it. `ef35100f1d4` added
the facade (extern `rt_gpu_provider_device_identity_raw`, struct
`GpuProviderDeviceIdentity`, 64-byte ABI read); the merge kept the C owner
(`runtime_dynload.c`), the header and the provider export and dropped the Simple
half. Restored verbatim. Red/green: `test/01_unit/lib/nogc_sync_mut/gpu/provider_spec.spl`
5/6 (`function gpu_provider_device_identity not found`) -> 6/6; native-build
`failed=1` -> `failed=0`.

### Blocker 8 (open) — the seed cannot link a GPU-capable non-bootstrap entry

After compile, the link is refused: `239 runtime symbol(s) referenced by
generated code have no definition` — 84 `rt_vulkan_*`, 16 `rt_gpu_provider_*`,
40 `rt_metal_*`, 37 `rt_cuda_*`, 28 `rt_rocm_*`, 10 `rt_oneapi_*`, 10
`rt_intel_*`, 8 `rt_engine2d_*`, 3 `rt_webgpu_*`, `rt_opengl_*`, `rt_font_load_array`,
`rt_cpu_arch_name`. Measured lanes:

- default lane: links the core-C archive only; none of the above are in it.
- `--runtime-bundle host-gpu --runtime-path R`: needs
  `R/deps/libspl_hosted_runtime-*.rlib` (`find_hosted_runtime_rlib`); the
  nightly cargo here writes it to `release/build/spl_hosted_runtime/<hash>/out/`,
  so a plain cargo target dir is rejected with `host-gpu canonical hosted
  runtime rlib is missing`. With a hand-made `R`, the lane links its core-C
  "provider loader" supplement, which contains no `runtime_dynload.o`
  (`nm` shows no `rt_gpu_provider_*`) — the same 239 are reported.
- `libsimple_native_all.a` built with `--features vulkan`
  (`cargo build --release -p simple-native-all --features vulkan`, 122 s,
  4.5 GB RSS) defines 204 of the 239. `selected_runtime_library` admits it only
  for `bootstrap_main.spl` or the BootstrapTools lane
  (`reject_unexpected_native_all`); `rust-hosted` is a removed bundle.
- That archive also has 12 duplicate `rt_vk_*` definitions between
  `simple_native_all` and `simple_runtime` (needs `-z muldefs`).

Workaround used for the evidence below (NOT a sanctioned build; the binary is
diagnostic-grade): let the failed native-build keep its objects
(`.simple/native-objects-*`), then link by hand, Rust archive first so one
runtime owns the argv family, core-C supplement after it for the 12 C-only names:

```sh
clang++ -fPIC -no-pie -fuse-ld=lld -Wl,-z,muldefs -o vulkan_2d_qualification \
  $O/_main_stub.o $O/_init_all.o @$O/spl_objects.rsp \
  -Wl,-u,rt_function_not_found -Wl,-u,rt_set_args -Wl,-u,rt_string_bytes \
  $NATIVE_ALL/libsimple_native_all.a $O/host_gpu_core_c_runtime/libsimple_runtime.a \
  -Wl,--gc-sections -lpthread -ldl -lm -lz -lzstd -ltinfo \
  -L/home/yoon/.local/lib -l:libvulkan.so.1
```

Core-C first instead gives a binary whose `sys_get_args` (C) never sees what
`rt_set_args` (Rust) stored: every invocation prints the usage line. Result:
31.7 MB, sha256 `8d47265c5de8bb21a0eb2c86caf4179edbd4bcd2c9fa903d7be35d1ec5533c96`,
kept at `/home/yoon/skia-n2/artifacts/nb_manual_20261122/vulkan_2d_qualification`.
Real fix: a seed (or self-hosted) runtime lane that links the Vulkan runtime
and the provider registry for an ordinary entry.

### Skia leg: green on the GB10 for three web scenes

`worker-skia-*` with the 2026-11-18 provider (`758f717f…bc89`), NVIDIA ICD.
Skia rasterises the DrawIR Simple's web renderer produced from the scene HTML;
the device readback digest equals the Simple oracle digest:

| scene | size | Skia `pixel_sha256` = oracle | tries |
|---|---|---|---|
| web-box (`web-opaque-box-v1`) | 16x16 | `204df3a7…7817` | 1 |
| corpus-case01 | 640x480 | `2f4d3fb1…39e9` | 1 |
| corpus-case06 | 640x480 | `0372ef52…ebb1` | 2 |
| corpus-case02 | — | blocked: `skia-owner:upstream Skia corpus case 02 edge oracle mismatch` (3 of 4 tries; 1 `Vulkan device or Ganesh context unavailable`) | 4 |

Receipts carry `physical_device_uuid: 1883ff9c30a91b8abc50ef34ac2f5a89`,
`driver_uuid: 6d5e1e18…c390`, `device_type: integrated` — the restored identity
facade attests the GB10. Case 02 is the known
`skia_case02_edge_tolerance_exceedance_2026-09-27.md`. Blocker 5 does not apply
to a native executable. Gate: `scripts/check/check-skia-web-reference-compare.shs`
(PASS 3 scenes; FAIL on case 02).

### Blocker 9 (open) — native Engine2D leg: device identity empty

`worker-engine2d-web-box` in the same executable, 3 of 3 runs and through
`run-web-box`:

```
status=blocked reason=engine2d-capture:selected Vulkan physical device identity unavailable
```

Strict submit, readback and the device-type/driver checks before it pass, so
`rt_vulkan_selected_device_identity_v1(expected_device)` returned a string the
facade rejects. Ruled out: the symbol is the real Rust one (`nm -S`: 0x618
bytes, not the C weak stub); the `v1:<hex>:<hex>` split and hex validation
behave identically natively and interpreted (probe on a literal). Not yet
checked: whether `session.device` (from `vulkan_get_device()`) still equals the
runtime's `selected_device_token` at capture time (a re-select bumps the
token), and `device_generation_quarantined`. Until this is fixed there is no
Engine2D-vs-Skia pixel comparison on the physical device; `run-*` cannot PASS.
