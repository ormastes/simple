# Linux GB10 N2 qualification attempt — Simple 2D vs upstream Skia

Date: 2026-11-18. Host: physical Linux aarch64, NVIDIA GB10 (DGX Spark class).
Scope: `doc/08_tracking/todo/simple_2d_skia_renderdoc_linux_n2_2026-09-27.md`.
**Outcome: build and device rows qualified; worker/pixel rows BLOCKED.**
Artifacts live on the host under `/home/yoon/skia-n2/artifacts/` (outside any worktree, not committed);
only this report and the provider receipt copy are tracked.

## Device identity (qualified)

Probe: a 40-line C `vkCreateInstance`/`vkGetPhysicalDeviceProperties2`/
`vkCreateDevice` program (`/home/yoon/skia-n2/artifacts/vkprobe.c`), run with
`VK_DRIVER_FILES=/usr/share/vulkan/icd.d/nvidia_icd.json`. Receipt:
`/home/yoon/skia-n2/artifacts/device_identity.txt` (regenerated 2026-11-17T18:46:32Z, identical identity).

| field | value |
|---|---|
| OS / kernel | Ubuntu 24.04.4 LTS, Linux 6.17.0-1032-nvidia aarch64 |
| device | `NVIDIA GB10`, type 1 (integrated GPU), vendor `0x10de`, device `0x2e12` |
| driver | `NVIDIA` 580.173.02 (`driverVersion` `0x912b4080`) |
| Vulkan API | 1.4.312 |
| deviceUUID | `1883ff9c30a91b8abc50ef34ac2f5a89` |
| driverUUID | `6d5e1e1841115cbdae1ec369f9e3c390` |
| ICD manifest | `/usr/share/vulkan/icd.d/nvidia_icd.json`, sha256 `7bdb6f27…a34b` |
| loader | `/home/yoon/.local/lib/libvulkan.so.1` → 1.4.328, sha256 `b066e542…cbfe7` (picked up by `LD_LIBRARY_PATH`, not the system loader) |

The physical device enumerates as the only device under the NVIDIA ICD;
lavapipe is a separate ICD and was never selected for the rows below except
where stated.

## Pinned Skia provider build (qualified, build-only)

- Checkout: `/home/yoon/skia-n2/skia`, shallow fetch of exactly
  `35d5edfa0d50984c22ff94f5438c31e0db12c6f8`, clean worktree.
- Dependencies: `tools/git-sync-deps` with the pinned `DEPS`; 45 Git
  checkouts attested by `verify-skia-deps.shs`, manifest digest
  `28e98416c16419a904936309ec00667df6bf0a1058ac0ab55229e1353c90c666` —
  byte-identical to the 2026-09-27 macOS attestation.
- Build: `SIMPLE_UPSTREAM_SKIA_ENABLE_AFFINE_V3=1 SIMPLE_UPSTREAM_SKIA_NINJA_JOBS=6
  CC=clang CXX=clang++ AR=llvm-ar sh tools/upstream-skia-ganesh-vulkan/build-linux.shs`,
  clang 23.1.0 + lld 23.1.2, under `systemd-run --scope -p MemoryMax=10G`.
  1308 ninja targets; libskia.a step ~2 min wall at `-j6`; peak RSS 0.93 GB.
- Receipt: `doc/09_report/linux_gb10_skia_provider_receipt_2026-11-18.json`
  (also at `/home/yoon/skia-n2/artifacts/libsimple_upstream_skia_ganesh_vulkan.so.receipt.json`,
  sha256 `2c46ae5d5174cc8a35f7c763f9c10150ae229c5df7f58ee179602770c2113ee8`).

| artifact | sha256 |
|---|---|
| `DEPS` | `f1b15cb2100a88b91e55719afe2179591392df99a60c4403e90f4b92a16f0724` |
| `libskia.a` (419,128,148 B) | `f368cf7b213c99f7826d5478e30a2d30aed5243cb5a7409bcc567b994860f60a` |
| provider `.so` (106,494,000 B, `affine_v3_enabled=1`) | `758f717f521fe4e996f41170a0cd70b53492c94df92d01d570f45f262605bc89` |

A second invocation (`ninja: no work to do`) relinked the provider to the same
digest; that shows a deterministic relink, not a from-scratch reproducible
build. Every Skia object carries only the `clang version 23.1.0` comment; the
provider's `.comment` also lists `GCC: (Ubuntu 13.3.0)`, which comes from the
system C runtime start files, and it links the system `libstdc++.so.6` and
`libgcc_s.so.1`. No GCC compiler was invoked.

`build-linux.shs` needed four host fixes on this aarch64 host (all in `.shs`):
1. GN defaults `cc="cc"`/`cxx="c++"` resolve to `aarch64-linux-gnu-g{cc,++}-13`;
   the script now names clang/clang++/llvm-ar (overridable by `CC`/`CXX`/`AR`).
2. No system fontconfig/freetype2 headers: `skia_use_fontconfig=false
   skia_use_system_freetype2=false` (bundled FreeType; the provider renders no text).
3. No `libvulkan.so` dev symlink and no `/usr/include/vulkan`: link
   `-l:libvulkan.so.1` and compile with Skia's in-tree headers
   (`-DSK_USE_INTERNAL_VULKAN_HEADERS`), as `build-macos.shs` already did.
4. Sync only when the checkout is not already attested (as on macOS) and an
   opt-in `SIMPLE_UPSTREAM_SKIA_NINJA_JOBS` bound.

The receipt now records `gn_args` (the feature configuration, unchanged and
still pinned by the qualification runner) and a separate `gn_host_args`
(toolchain + font plumbing). **Known gap:** the runner validates only
`gn_args`; `gn_host_args`, `cxx_version` and `platform` are recorded but not
checked.

Disk note: after the build, the unused `third_party/externals/unicodetools`
(3.2 GB) and `swiftshader` (1.4 GB) checkouts and `out/.../obj` (~1 GB) were
deleted for host disk pressure. The receipt above was produced before that;
the checkout must be re-synced before `verify-skia-deps.shs` attests it again.

## Pure-Simple qualification executable (BLOCKED)

No self-hosted pure-Simple release binary exists on this host
(`bin/release/` absent), so the blend seed was used:
`/home/yoon/.cache/cargo-target-webrender-blend/release/simple`, sha256
`119feb0f865390b5dabb084e8b3ec94a4e5dbb391ffae2339b9af6fc7bd01b91`
(prints the "bootstrap seed only" banner).

- Failing-assertion control: a one-line spec `expect(1).to_equal(2)` exited 1,
  `Results: 1 total, 0 passed, 1 failed`, naming `expected 1 to equal 2`; the
  passing twin exited 0 (control logs lost, see Regeneration; spec sources at `/home/yoon/skia-n2/artifacts/controls/`). The seed's SPipe
  verdicts are therefore not vacuous.
- `native-build` of `src/app/test/vulkan_2d_qualification/main.spl` with the
  README recipe (`native-build --source src/compiler --source src/app
  --source src/lib --entry-closure --entry …/main.spl --strip`, `MemoryMax=16G`)
  produced **no binary within the 2 h cutoff**. The seed runs the build as an
  interpreted Simple driver: ~65 min of single-threaded front-end work (RSS
  ~2.6 GB, log silent after load warnings), then a child
  `simple run src/app/cli/native_build_worker.spl` still at 100 % CPU and
  4.1 GB RSS after 58 min. Log lost, see Regeneration. It was left
  running at the cutoff; this is a throughput blocker of the seed native-build
  path, not a diagnosed compile error.
- Hedge without `--source src/compiler` (`SIMPLE_NATIVE_BUILD_TRACE=1`,
  `MemoryMax=6G`): OOM-killed by its scope after 29 s.
- Seed-hosted worker fallback (`simple run main.spl worker-skia-corpus-case01 …`,
  which would only ever be candidate-grade): the interpreter rejects the
  runner at `main.spl:67:9` with `semantic: value is not callable`
  (`if val actual = file_hash_sha256(path)`), after the JIT fell back on an
  ambiguous `getpid` (two co-compiled definitions in `io/sysinfo_ops.spl` and
  `io_runtime.spl`). Re-run log: `/home/yoon/skia-n2/artifacts/seed_worker_case01.log`.

Consequently `01-solid-boxes`, `06-rectangular-clip` and `02-fractional-edges`
have **no Engine2D or Skia worker readbacks on GB10**. Their rows stay
`not-run`; no pixels were compared and no tolerance verdict exists.

## RenderDoc on GB10 (generic Engine2D scene captured; N2 workers not capturable)

- Re-verified the 2026-11-14 note "GB10 rejects `vkCreateDevice` under the
  RenderDoc layer": it is **intermittent**, not a hard rejection. Bare
  instance+device probe, six attempts each: no layer 6/6 ok; layer via
  `ENABLE_VULKAN_RENDERDOC_CAPTURE=1` 2/6 ok (others `-3`,
  `VK_ERROR_INITIALIZATION_FAILED`); under `renderdoccmd capture` 0/6 in one
  batch, 6/6 in the next. Cause not established; two unrelated processes held
  ~21 GB of GPU memory at the time (correlation only).
- `rdoc_capture_simple_vulkan` (`renderdoc_vulkan_capture.spl`, seed above,
  RenderDoc v1.36 via an installed-tree shim, NVIDIA ICD): try 1 failed all
  5 Engine2D `vkCreateDevice` retries with `-3`; tries 2 and 3 **passed**,
  `num_captures=1`. Converted XML names vendor 4318 (`0x10de`), device 11794
  (`0x2e12`), `NVIDIA GB10`, driver `580.173.02`; 3 compute dispatches.

| capture | bytes | sha256 |
|---|---|---|
| original try 2 (lost, see Regeneration) | 7457 | `ad576b2a8502010317b197d41b3b0f6a4c19d2f37bacebd100db385063bcba45` |
| original try 3 (lost, see Regeneration) | 7616 | `b18190d11030a7ae3eb99ca5a7dab3fb8a751c84ab0bbae7a2a5b2870a6870b2` |
| `/home/yoon/skia-n2/artifacts/renderdoc/engine2d_gb10_try2/simple_gui_app-20261117T184639Z-2096362_capture.rdc` (regenerated) | 7457 | `ab1bd6af7e0b35749d0e1963a0f6fc0d5cf22dfc61aae0e69f145dccc709e3a9` |

This is the generic capture scene, not an N2 case. The qualification runner
and `provider.cpp` never call the RenderDoc in-app start/end API and never
present, so even with a working executable the N2 workers produce no `.rdc`;
that is a separate blocker.

## Regeneration (2026-11-18, follow-up)

The original `build/` artifacts were lost to a worktree cleanup: the landing
helper's `git worktree remove` deleted the gitignored `build/` tree. That
removed the provider `.so`, logs, captures and `device_identity.txt`, and
killed the still-running seed `native-build`. They were regenerated outside
any worktree, under `/home/yoon/skia-n2/artifacts/`:

- Provider relinked from the surviving `libskia.a` (`f368cf7b…f60a`) with the
  exact compile/link line of `build-linux.shs` (no Skia re-sync, because the
  dependency checkout was partly deleted for disk). The command is in
  `/home/yoon/skia-n2/artifacts/relink.log`. The result `/home/yoon/skia-n2/artifacts/libsimple_upstream_skia_ganesh_vulkan.so`
  has sha256 `758f717f521fe4e996f41170a0cd70b53492c94df92d01d570f45f262605bc89`,
  the same as the original build.
- `device_identity.txt` regenerated with the same probe; the identity is unchanged.
- RenderDoc: one new capture of the generic Engine2D scene on the GB10 (NVIDIA
  ICD). Loop try 1 did not run at all: the log directory did not exist yet,
  which was a harness mistake and not a device result. Try 2 passed first time
  with no `vkCreateDevice` retries: `num_captures=1`, `record_valid=1`,
  pixel hash `694777e1…c52f`. Replay-open evidence is in
  `/home/yoon/skia-n2/artifacts/renderdoc/engine2d_gb10_try2/replay_open.txt`: `renderdoccmd convert`
  opened the capture (rc 0, 58 chunks, 3 `vkCmdDispatch`) and it names vendor
  4318, device 11794, `NVIDIA GB10`, driver `580.173.02`.
- The seed-hosted worker failure was re-run at `0d4cd599298`, with the same
  error. Both blockers are filed in
  `doc/08_tracking/bug/linux_gb10_n2_qualification_executable_blockers_2026-11-18.md`.
- The native-build log and the control logs were not regenerated. The 2 h
  native-build is the filed blocker, and the controls are summarised above.

## Row summary

| row | status |
|---|---|
| Physical Linux Vulkan device identity (OS, GPU, driver, API, UUIDs) | PASS |
| Pinned Skia checkout + 45 attested deps | PASS |
| Provider build, `affine_v3=1`, receipt + digests | PASS (build-only) |
| Failing-assertion control (seed) | PASS |
| Native qualification executable | BLOCKED (see above) |
| `01-solid-boxes` Engine2D/Skia exact RGBA on GB10 | not-run (blocked: runner `not callable` fixed; now web admission `background-position-x`, see bug doc Blocker 3) |
| `06-rectangular-clip` Engine2D/Skia exact RGBA on GB10 | not-run (blocked) |
| `02-fractional-edges` vs declared tolerance on GB10 | not-run (blocked) |
| RenderDoc capture on GB10 (generic Engine2D scene) | PASS (2 of 3 tries; regenerated 1 of 1 attempted) |
| RenderDoc capture of N2 case workers | BLOCKED (no in-app capture hook) |
| `31-latin-shaping`, GUI input, SPipe/docgen gates | not-run |
