# Linux GB10 N2: no runnable qualification executable (seed native-build stall + interpreter "value is not callable")

- **Filed:** 2026-11-18
- **Status:** open (2, 3, 4, 7 and 9 fixed; 1 diagnosed with a workaround; 8 and 10 open; 5 and 6 are interpreter-only — see the 2026-11-22 and 2026-11-23 sections)
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

## 2026-11-23 — Blocker 9 root cause and fix; Engine2D-vs-Skia pixel comparison on the GB10

Branch `work/webrender-skiadev-20261123` (base release/1.0.0 `ccb5a2ef29c`).

### Blocker 9 (fixed) — the native code split a raw `char*`

**The token and generation hypotheses are wrong.** With `gdb` `dprintf` on the
diagnostic binary, the token sequence is:

- `rt_vulkan_init`
- `rt_vulkan_select_device(0)`
- `rt_vulkan_get_device` returns 2
- `rt_vulkan_selected_device_identity_v1` is called with `expected_token=2`
- `rt_vulkan_get_device` returns 2 again

So the device token matches. The device was not enumerated twice and there is
no re-select.

**The bug is at the call site.** The facade
`vulkan_sffi_selected_device_identity_v1` disassembles to:

```
ebc660: blr rt_vulkan_selected_device_identity_v1   ; returns *const c_char
ebc67c: blr rt_string_new_literal                    ; ":"
ebc690: blr rt_string_split                          ; receiver = the raw char* <- bug
```

`vulkan_sffi_device_name` makes the same kind of call, then
`blr rt_cstring_to_text`. The Rust runtime returns `*const c_char` for every
GPU name, type and identity query. The seed decodes a C-string return only for
the names in `C_STRING_RETURNING_RUNTIME_FNS` (`codegen/instr/calls.rs`), a list
from the 2026-08-20 census. `rt_vulkan_selected_device_identity_v1` was added
after that census, so it is in neither that list nor `runtime_sffi.rs`. (The
interpreter extern `rt_vulkan_selected_device_identity_v1_fn` deliberately
returns "" — it cannot attest the native device owner — so the interpreted
lane is blocked by design and never exercised this decode.)

**Census re-run 2026-11-23.** Rust `extern "C" fn rt_* -> *const c_char` (19
symbols) intersected with Simple `extern fn ... -> text` gives 12 symbols. All
were already listed except this one.

**Fix.** `C_STRING_RETURNING_RUNTIME_FNS` and the
`RuntimeFuncSpec("rt_vulkan_selected_device_identity_v1", [I64], [I64])` entry
in the seed.

- **Red:** `cargo test -p simple-compiler --lib cstring_returns` gave 3/5. The
  new `cstring_returns_native_decodes_selected_device_identity_v1` found 0
  `rt_cstring_to_text` relocations where 1 was expected.
- **Green:** 5/5, and 42/42 together with the `runtime_sffi` tests.
- **Rebuilt facade:** `e4b3f0: blr rt_vulkan_selected_device_identity_v1` is
  now followed by `e4b3fc: blr rt_cstring_to_text`.

**Pure-Simple backend: unverified.** No C-string decode list was found in
`src/compiler/` (grep for the 12 names and `rt_cstring_to_text`). Whether the
self-hosted native backend decodes these returns some other way is unverified.
Filed as `doc/08_tracking/bug/selfhosted_native_cstring_extern_return_decode_unverified_2026-11-23.md`.

### Executable used for the evidence (diagnostic-grade, Blocker 8 unchanged)

- **Seed:** private seed with the fix, built with clang and lld:
  `CC=clang CXX=clang++ AR=llvm-ar`, linker `clang -fuse-ld=lld`,
  `CARGO_TARGET_DIR=~/.cache/cargo-target-wr-skiadev`.
  **Trap: `cc` on this host is GCC 13.** A cargo build without `CC=clang`
  compiles its C build scripts with GCC.
- **Native build:** `SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_CACHE_SCOPE=wr-skiadev-20261123 <seed> native-build ...`
  (same recipe as above). Result: `compiled=508 failed=0`, 30.99 s, 1.57 GB.
  The link was then refused with the same 239 missing runtime symbols.
- **Hand-link:** the 2026-11-22 recipe, but with the default lane's
  `$O/core_c_runtime/libsimple_runtime.a` in place of the host-gpu supplement.
  It resolves the same way: 0 undefined symbols, and the strong Rust
  `rt_vulkan_selected_device_identity_v1` (0x618 bytes) beats the C weak stub.
  The Rust archive is `~/.cache/cargo-target-wr-nativeall/release/libsimple_native_all.a`
  (2026-11-22, `--features vulkan`).
- **Binaries:**
  - `/home/yoon/skia-n2/artifacts/nb_skiadev_20261123/vulkan_2d_qualification`,
    sha256 `564c5ef8…94ec`, built from `d3fe115c87b`. The first results below
    came from it.
  - `./vulkan_2d_qualification_b113785`, sha256
    `98ea91fe0a9fe4d4712e5a4d7af82fb397a4a55a82c1e057a952b0e23b5dbd93`, built
    from `b11378538ed`. It adds the fallback-reason diagnostic, and its re-run
    gave the same table. `check-skia-web-reference-compare.shs` with this binary:
    `PASS — 3 scene(s) compared, upstream Skia readback equals the Simple web oracle, 0 mismatching`.
    That script covers only the Skia leg; the Engine2D leg is covered by `run-*`.
  It is NOT a sanctioned build. The missing piece is still a seed or
  self-hosted runtime lane that links the Vulkan runtime (`rt_vulkan_*`,
  `rt_engine2d_*`) and the provider registry (`runtime_dynload.o`,
  `rt_gpu_provider_*`) for an ordinary, non-bootstrap entry.

### Results: Engine2D vs upstream Skia on the physical GB10

Both legs ran on the NVIDIA ICD with provider
`/home/yoon/skia-n2/artifacts/libsimple_upstream_skia_ganesh_vulkan.so`. Each
`run-*` starts two fresh worker processes and compares their readbacks byte for
byte.

| scene | `run-*` | Engine2D rgba sha256 | Skia rgba sha256 | oracle | tries |
|---|---|---|---|---|---|
| web-box | **pass** (`pair_exact_rgba: pass`) | `204df3a7…7817` | `204df3a7…7817` | `204df3a7…7817` (Simple web oracle; the comparison record carries `oracle_rgba_sha256: none`) | 1 |
| corpus-case01 | **pass** (`pair_exact_rgba: pass`) | `2f4d3fb1…39e9` | `2f4d3fb1…39e9` | `2f4d3fb1…39e9` | 1 |
| corpus-case06 | blocked (Blocker 10) | — | (not run: the Skia worker starts only after Engine2D succeeds) | `0372ef52…ebb1` | 4 of 4 |

- **Engine2D receipts attest the GB10:** `device_name: NVIDIA GB10`,
  `device_type: integrated`,
  `physical_device_uuid: 1883ff9c30a91b8abc50ef34ac2f5a89`,
  `driver_uuid: 6d5e1e1841115cbdae1ec369f9e3c390`, `readback_source: device_readback`.
  This is the same UUID that `nvidia-smi -L` reports.
- **Repeatability:** `worker-engine2d-web-box` gave `status=candidate` 3 of 3.
  The 2026-11-22 binary gave the identity error on the same command.

### Blocker 10 (open) — corpus-case06: the strict Vulkan lane rejects a clipped plain rect

The worker now appends the submit fallback reason to a capture failure. That
is a `main.spl` diagnostic only; no check was relaxed. The failure reads:

```
status=blocked reason=engine2d-capture:Engine2D strict Vulkan owner receipt incomplete (fallback: strict-vulkan-command-preflight-required)
```

- **Not a regression.** The 2026-11-22 binary fails the same way on case 06.
  It never reached the identity query, so "3/3 scenes blocked at identity" was
  true only for web-box.
- **Source:** `_engine2d_draw_ir_strict_vulkan_primitive_reason`
  (`engine2d/draw_ir_adv.spl`) admits `clip_rect` only on an affine coverage
  rect ("any other clipped command still fails closed"). Case 06 is
  `corpus-case06-rectangular-clip-only`, so all of its clipped commands are
  plain rects.
- **Fix design (not done here):** give the plain-rect kernel the same
  surface-space clip that the affine coverage kernel already has, as a scissor
  in its push constants. Then admit `clip_rect.present` for `DRAW_IR_COMMAND_RECT`.
- **Rejected:** intersecting the clip into the rect on the host is exact only
  for a solid, integer-aligned fill. It would quietly narrow the scope of the
  strict lane.
- **Red spec to write first:** a strict-Vulkan submit of a 1-command clipped
  rect must give `fallback_required=false`. The pixels must match the case 06
  oracle `0372ef52…ebb1`.

### Seed lib suite with the fix

Command: `cargo test --release -p simple-compiler --lib` (clang/lld env).

- **With the fix:** 5041 passed, 11 failed, 5 ignored.
- **Base `ccb5a2ef29c`:** the same 11 tests, run alone, give 10 FAILED.
- **The 11th** (`enum_discriminant_abi_tests::seed_builtin_discriminants_are_the_declared_ordinal`)
  passes alone on both base and fix, twice each. It is an order-dependent flake
  under the full parallel run.
- **No failure is caused by this change.** The 10 base failures are
  `collection_capture`, 2 `mir::reachability`, 6 `pipeline::native_project`
  (bootstrap capsule ABI, core-lane ABI, hosted bundle, partial archive, object
  cache slice, lsp-mcp startup) — plus `value::tests::shared_text_unicode_index_and_slice`.

## 2026-11-23 (later) — Blocker 10 fixed: strict Vulkan clips plain rects; 3 of 3 scenes byte-identical Engine2D vs Skia

Branch `work/webrender-vkclip-20261123` (base release/1.0.0 `f9994a57f03`, which
carries the Blocker 9 seed fix from PR #10940).

### Fix (pure Simple, no shader change)

The plain-rect compute kernel already had a scissor. `_pack_rect_pc` packs
`clip_x/y/w/h/clip_enabled` into its push constants, and the GLSL rect kernels
discard pixels outside the scissor. The strict lane never set it.
`engine2d/draw_ir_adv.spl`:

- **Preflight** (`_engine2d_draw_ir_strict_vulkan_primitive_reason`) now admits
  `clip_rect.present` on a non-affine command only when all of these hold: it
  is a `DRAW_IR_COMMAND_RECT`, it is not the first command, and the clip width
  and height are not negative.
- **Still fail closed:** a clipped first command (it is executed as
  `eng.clear`, which ignores the clip), clipped text, edge and path commands
  (their strict executors apply no clip), and a negative clip. All of them
  still return `strict-vulkan-command-preflight-required`.
- **Executor** (`_engine2d_draw_ir_execute_strict_vulkan_primitives`): for a
  plain or fractional rect, it calls `eng.set_clip(clip)` before
  `draw_rect_filled` and `eng.clear_clip()` right after.

The damage entry (`..._strict_vulkan_submit_damage_with_images`) shares the
preflight. It replays through the general renderer, which already applies
`command.clip_rect` through `set_clip`. No `*-spirv-pinned` row is affected.

### Red to green

`test/01_unit/lib/gc_async_mut/gpu/engine2d/strict_vulkan_clipped_rect_spec.spl`
runs on lavapipe (`VK_DRIVER_FILES=lvp_icd.json`).

- **Red:** 2/6 passed (`cb4f6d46439`). The failures were real:
  `strict-vulkan-command-preflight-required` and `pixels == []`.
- **Green:** 6/6 passed (`4b5cd5eeffe`), in 63 s with 3.2 GB maximum RSS.

The spec covers:

- an 8x6 scene where the clip cuts a rect on all four sides, followed by an
  unclipped rect outside the clip that proves the clip is restored; the pixels
  are given exactly;
- the same scene compared with the CPU engine;
- a clipped fractional rect;
- the negative cases above;
- **corpus case 06 at its full 640x480**: strict Vulkan readback equals the CPU
  engine and the oracle `0372ef52…ebb1`. One cyan pixel, `0xff00aaff`, is
  checked first.

Neighbouring specs are unchanged: `strict_vulkan_fractional_rect` 2/2,
`strict_vulkan_affine_coverage` 3/3, `final_output_capture` 8/8.

### Physical GB10: Engine2D vs upstream Skia

**Executable**

The recipe is the one from the earlier 2026-11-23 section. The seed source has
no diff from `6596560270f`, so the fixed seed (sha256 `73ee310b…7680`) was
copied to the private `~/.cache/cargo-target-wr-vkclip`.

1. `SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_CACHE_SCOPE=wr-vkclip-20261123
   CC=clang CXX=clang++ AR=llvm-ar` native-build gave `compiled=511 failed=0`
   in 27 s with 1.48 GB RSS. The link was then refused with the same 239
   symbols (Blocker 8 is unchanged).
2. Hand-link (`libsimple_native_all.a` first, then the default lane's
   `core_c_runtime/libsimple_runtime.a`).

Result: `/home/yoon/skia-n2/artifacts/nb_vkclip_20261123/vulkan_2d_qualification`,
sha256 `e7c05e557f06d355fdf09ac7f13cb9b63b88fb01b89f77ec54d3fa7c34d3f68e`. It is
diagnostic-grade, for the Blocker 8 reason given above.

**Results**

Run with `check-vulkan-2d-qualification.shs <bin> <provider> <out> <scene>` on
the NVIDIA ICD. Receipts carry `physical_device_uuid: 1883ff9c30a91b8abc50ef34ac2f5a89`.

| scene | `run-*` | Engine2D = Skia = oracle sha256 | tries |
|---|---|---|---|
| web-box | **pass** (`pair_exact_rgba: pass`) | `204df3a7ca11c4633399761142e60ec5f3775aefe7e91a74863f107b9b647817` | 1/1 |
| corpus-case01 | **pass** | `2f4d3fb17e0a1ab65cba1f3b3950f1cf67b51f2f09df5faac247c2dc858039e9` | 1/1 |
| corpus-case06 | **pass** (was blocked, Blocker 10) | `0372ef52c5e58dfa59d71239609526592e022a00419f25e3eebc902d083debb1` | 3/3 |

Blocker 10 is closed. What remains open: Blocker 8 (no sanctioned link lane for
a GPU entry) and case 02 (Skia edge tolerance).

## 2026-11-23 (later) — Blocker 8: a sanctioned link lane, with no hand-link

Branch `work/webrender-gpulink-20261123`, rebased on release/1.0.0 `3b2c8d8959c`
(includes #10950 vkclip).

### Root causes

There are two root causes. The second one was found only after the first was
fixed.

1. **No lane admits the Vulkan runtime for an ordinary entry.**
   - `core-c-bootstrap` links the C weak stubs (`SPL_HOSTED_UNAVAILABLE_WEAK`
     in `runtime_native.c`).
   - `host-gpu` is the core-C loader plus the hosted rlib. The Vulkan provider
     DSO path covers only 4 `rt_vulkan_*` trampolines.
   - `selected_runtime_library` refused `libsimple_native_all.a` for any entry
     other than bootstrap or bootstrap-tools.
2. **On aarch64 the seed weak-stubbed libc.** `PlatformLinkConfig::linux()`
   scanned only `/lib/x86_64-linux-gnu/*.so`.
   - With native_all linked, the stub generator emitted 177 weak stubs
     (`__memcpy_chk`, `glob`, `accept4`, `_Unwind_RaiseException`, …), and the
     executable exported them.
   - Inside the NVIDIA ICD they interposed libc: `rt_vulkan_init` hit SIGSEGV
     in `eglGetProcAddress` (libGLX_nvidia, gdb backtrace).
   - The hand-link never ran the stub generator, which is why it worked.

### Fix

**1. A new explicit lane, `--runtime-bundle host-gpu-native-all`.** It is
never inferred, and it is also accepted through `SIMPLE_NATIVE_RUNTIME_BUNDLE`.
Code: `pipeline/native_project/config.rs` and `linker.rs`.
- **Archive:** `<runtime-path>/libsimple_native_all.a`, built with
  `cargo build --release -p simple-native-all --features vulkan`.
- **Admission:** the archive is admitted only if it defines `rt_vulkan_init`
  and `rt_gpu_provider_loaded`. Otherwise the lane fails closed and names the
  cargo command.
- **Link order:** native_all first, then the core-C supplement.
- **SQLite:** the external `-lsqlite3` is omitted unless the entry objects
  reference sqlite. The qualification binary's `NEEDED` list is `libm`,
  `libstdc++`, `libgcc_s` and `libc`; `libvulkan` is dlopened by ash.
- **Strict link required:** the lane requires `SIMPLE_NO_STUB_FALLBACK=1`, the
  strict final link with no stubs and no `ignore-all`. The nm preflight counts
  36 dead pre-GC references (`rt_metal_*`, `rt_oneapi_*`, `rt_intel_*`, …), so
  only the GC-aware lld link is authoritative here.
- **Other lanes:** `host-gpu`, `auto`, `simple-core` and `core-c-bootstrap` are
  unchanged.

**2. `native_all`: the 12 `rt_vk_*` noop stubs are now
`#[cfg(not(feature = "vulkan"))]`.** The vulkan archive now defines each of
them once, so `-z muldefs` is gone.

**3. `PlatformLinkConfig::for_target` uses the target's multiarch libc
directory.** aarch64 and riscv64 lists also include `libgcc_s.so.1`. This fix
is independent of the lane: under the strict link that the lane requires, the
stub generator emits only aliases, so the lane never stubs libc either way. It
fixes every non-strict aarch64 Linux link. For example, a default-lane hello
world on the base seed generated 61 libc weak stubs. On the new seed it
generates 0, and it still runs (`hello argc=2 last=world`).

**4. Pure-Simple linker.** `native_runtime_bundle_is_known` accepts the bundle,
and `native_runtime_archive_names` selects `libsimple_native_all.a` alone. This
path has **not been verified end to end**: no pure-Simple native link of the
qualification was run.

**5. Architecture.** A *proposed* amendment, awaiting an owner decision, was
added to `doc/04_architecture/runtime/default_native_runtime_shift_to_c_core_abi.md`.

### Red/green

**Probe** (`probe/main.spl`; the source, build scripts and logs are under
`/home/yoon/skia-n2/artifacts/nb_gpulink_20261123/evidence/`):

```
extern fn rt_vulkan_init() -> i64
extern fn rt_vulkan_device_count() -> i64
extern fn sys_get_args() -> [text]

fn main() -> i64:
    val args = sys_get_args()
    val init = rt_vulkan_init()
    print "probe argc={args.len()} last={args[args.len() - 1]} vk_init={init} vk_devices={rt_vulkan_device_count()}"
    0
```

- **Base seed, default lane:** the link is refused (`rt_vulkan_init` has no
  definition). Without `rt_vulkan_init`, it links and prints `vk_devices=0`
  on the GB10, silently wrong.
- **Lane, non-strict, before fix 3:** SIGSEGV.
- **Lane on the final seed, `SIMPLE_NO_STUB_FALLBACK=1`:** 0 stubs, and it
  prints `probe argc=2 last=hello vk_init=1 vk_devices=1`.
- **Lane without `SIMPLE_NO_STUB_FALLBACK=1`:** refused with
  `host-gpu-native-all requires SIMPLE_NO_STUB_FALLBACK=1`.
- **New seed, default lane:** still refuses the probe.

**Unit tests:**
- **Rust red:** a compile failure, since `NativeRuntimeLane::HostGpuNativeAll`
  did not exist.
- **Rust green:** `cargo test --release -p simple-compiler --lib native_project`
  gives 435 passed and 6 failed. All 4 new lane tests pass. The 6 failures
  match, by name, the 6 `pipeline::native_project` base failures listed in this
  doc's "Seed lib suite with the fix" section: capsule ABI, core-lane ABI,
  hosted bundle, partial archive, object cache slice and lsp-mcp startup. They
  were not re-run on base here.
- **`simple-common` `link_config`:** 8 of 8 pass, including the new
  `linux_system_scan_libs_follow_target_arch`.
- **Simple spec** (`test/01_unit/compiler/linker/native_link_hardening_spec.spl`):
  40/52 to 41/52. The new case was red before the `.spl` change. The 11
  remaining failures have the same names before and after the change.

**CLI.** `src/app/cli/native_build_main.spl` has no bundle-name validation; it
passes the bundle through. The seed CLI (`driver/src/cli/native_build.rs`) and
`native_build_sffi.rs` accept the new name.

### Sanctioned build and GB10 evidence

The seed and the `--features vulkan` archive are private
(`CARGO_TARGET_DIR=~/.cache/cargo-target-wr-gpulink`), built with clang and
lld. Both were built from this lane's commits on `1071a08692d`, before the
rebase. `git diff 1071a08692d 3b2c8d8959c -- src/compiler_rust src/runtime` is
empty, so the Rust and C inputs are identical. Build command:

```sh
SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_CACHE_SCOPE=wr-gpulink-20261123 \
  <seed> native-build --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/test/vulkan_2d_qualification/main.spl \
  --runtime-bundle host-gpu-native-all --runtime-path ~/.cache/cargo-target-wr-gpulink/release \
  --strip --output /home/yoon/skia-n2/artifacts/nb_gpulink_20261123/vulkan_2d_qualification
```

- **Build:** 8.2 s warm, 0.48 GB RSS, 0 stubs, 0 undefined `rt_*`.
- **Binary:** sha256 `400eb5c19ff8a7ef0487959788a9a5fb690694dafa6870f8ce3d14305b982ef5`.
- **Run:** NVIDIA ICD, provider `758f717f…bc89`, full resolution, one try each.

| scene | `run-*` | Engine2D = Skia rgba sha256 | equals hand-link / oracle |
|---|---|---|---|
| web-box | pass | `204df3a7ca11c4633399761142e60ec5f3775aefe7e91a74863f107b9b647817` | yes |
| corpus-case01 | pass | `2f4d3fb17e0a1ab65cba1f3b3950f1cf67b51f2f09df5faac247c2dc858039e9` | yes |
| corpus-case06 | pass | `0372ef52c5e58dfa59d71239609526592e022a00419f25e3eebc902d083debb1` | yes |

Receipts: `device_name: NVIDIA GB10`,
`physical_device_uuid: 1883ff9c30a91b8abc50ef34ac2f5a89`,
`readback_source: device_readback`, `pair_exact_rgba: pass`.

**corpus-case02 (checked, not fixed):** 2 of 2 runs gave
`engine2d-owner:Engine2D corpus case 02 edge oracle mismatch`. It now fails in
the Engine2D leg first, before Skia runs. Still open with
`skia_case02_edge_tolerance_exceedance_2026-09-27.md`.

### Status

Blocker 8 is fixed. The owner accepted the architecture amendment on
2026-11-23: native_all is admitted for a non-bootstrap entry only when the
`host-gpu-native-all` bundle is named explicitly.

## 2026-11-23 (later) — corpus case 02: the Engine2D leg is fixed; Skia's edge policy is still open

### Root cause: a native conversion defect, not edge AA

The oracle and the AA are correct. Under the interpreter, strict Vulkan output
for case 02 passes the analytic area oracle on both lavapipe
(edge_max=1, edge_sum=12/2742) and the NVIDIA GB10 ICD (edge_max=1, 6/2742).
Only the native executable failed.

A native probe on the GB10 printed the affine dispatch box as `(0,0,2,2)` for
both the tile and the bar. The correct boxes are `(33,38,196,126)` and
`(288,38,7,285)`. With those boxes nothing was painted (exact_mismatch=18288,
edge_excess=846, edge_max=219).

The cause is `floor_f64(min_x).to_i32()`. Natively, `.to_i32()` on an
f64-returning **call** converts the raw IEEE bits, so 47.0 becomes 0. Filed as
`native_call_result_f64_to_int_conversion_bits_2026-11-23.md` with a minimal
repro.

**Fix (pure Simple workaround, names the real fix):** `draw_ir_adv.spl` binds
the floor/ceil results to typed f64 locals before `.to_i32()`. It does this in
the affine box and in the fractional-rect pixel box. No check or tolerance
changed. The case 02 oracle-mismatch errors (Engine2D and Skia) now append the
verdict numbers, as a diagnostic only.

### Red to green

- **Red:** binary `nb_case02_20261123/qual_red`, sha256 `2504e05f…6cb2`, built
  from the rebased tree with no fix.
  `run-corpus-case02` → `engine2d-owner:Engine2D corpus case 02 edge oracle mismatch`.
- **Green:** the native probe gives `vk: passed=true exact_mismatch=0
  edge_excess=0 edge_sum=6/2742 edge_max=1`.
- **Spec:** `test/01_unit/lib/gc_async_mut/gpu/engine2d/strict_vulkan_case02_edges_spec.spl`
  (2/2 on lavapipe). It pins both dispatch boxes and checks the full
  640x480 strict-Vulkan readback against the oracle. It runs interpreted, so
  it was green before the fix too: the red evidence is the native run above.

### Sanctioned build and GB10 results

Built with the Blocker 8 recipe on `origin/release/1.0.0` after PR #11030:
`SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NO_STUB_FALLBACK=1 --runtime-bundle
host-gpu-native-all`, with no hand-link, clang, and 0 stubs. The seed is the
`cargo-target-wr-gpulink` seed. Its Rust and C inputs differ from HEAD in 30
files (cc_detect, const-default call sites, runtime pool and process tree); none
of them is in the Vulkan or Engine2D paths.

Binary: `/home/yoon/skia-n2/artifacts/nb_case02_20261123/vulkan_2d_qualification`,
sha256 `fc3f8d73f06c75764b9100da507c2ff17eacb4c3a35f03056e07b6462c2784a7`. Runs
used the NVIDIA ICD and provider `libsimple_upstream_skia_ganesh_vulkan.so`.

| scene | `run-*` | Engine2D rgba sha256 | Skia | tries |
|---|---|---|---|---|
| web-box | pass | `204df3a7…7817` | equal | 1/1 |
| corpus-case01 | pass | `2f4d3fb1…39e9` | equal | 1/1 |
| corpus-case06 | pass | `0372ef52…ebb1` | equal | 1/1 |
| corpus-case02 | blocked in the **Skia** leg | `962ca9e4a2cd2366bebd9f8db604803efab1df976f7a35f5fcd0d9fc5981c306` (Engine2D `status=candidate`, oracle pass) | `upstream Skia corpus case 02 edge oracle mismatch (exact_mismatch=0 edge_excess=4 edge_max=30 edge_sum=1004/2742)` | 3/3, identical each time |

The Skia numbers on the GB10 are the same as the 2026-09-27 macOS measurement:
4 edge pixels over 16 and a max delta of 30. They are deterministic Skia
coverage-AA edge policy, so the owner decision in
`skia_case02_edge_tolerance_exceedance_2026-09-27.md` still blocks a case 02
`run-*` pass. Even after that decision, a `pair_exact_rgba` comparison of
Engine2D (an ideal area sampler) against Skia cannot hold on the AA edges of
case 02.

Separate finding, not fixed here: the CPU engine's DrawIR composition skips v4
affine commands (`affine-or-raster-policy-unsupported`). Case 02 on the CPU
engine is therefore four white clears only.
