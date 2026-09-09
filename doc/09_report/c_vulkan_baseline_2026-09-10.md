# C Vulkan 2D baseline — 2026-09-10

## Verdict

`measured-unadmitted`. This is the C/reference side of the canonical
`vulkan_2d_c` showcase only. No Simple bootstrap, Simple renderer run, Chrome
builder, or cross-renderer ratio was run in this task. The comparator emitted
`compare_status=skipped` with
`compare_reason=c-leg-measured-unadmitted:receipt-needs-common-admission`.

## Canonical invocation

```text
sh scripts/check/check-vulkan-2d-c-compare.shs
```

The script selected the existing fixture and used these exact C build steps:

```text
glslangValidator -V test/05_perf/bench/vulkan_2d_c/rect.comp.glsl -o build/vulkan-2d-c-compare/rect.spv
clang -std=c99 -O2 test/05_perf/bench/vulkan_2d_c/vk2d_bench.c \
  -I/opt/homebrew/include -L/opt/homebrew/lib -lvulkan \
  -o build/vulkan-2d-c-compare/vk2d_bench
VK_ICD_FILENAMES=/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json \
  build/vulkan-2d-c-compare/vk2d_bench 800 600 64 300 1 5
```

The executed script's live contract was five untimed warmups, 300 timed
samples, 800×600, 64 rectangles loaded from the committed table, a retained
three-slot ring, and one post-timing full-frame capture. The corrected run
retained its complete producer streams and reported
`unconditional_submit_wait=false`, `timed_readback_bytes=0`,
`cpu_completion_wait_count=0`, and 300 fence completions through 865
nonblocking polls. The raw streams, projected receipt, toolchain identity,
and RSS evidence are bound below.

Here, `cpu_completion_wait_count=0` means no timed blocking Vulkan wait call.
The submission thread still polls (with a short sleep) when it must reuse a
busy ring slot; the 865 poll count exposes that completion gating rather than
mislabeling it as fully independent CPU progress.

## Measured row

| Field | Value |
|---|---|
| workload | `vulkan-2d-c-rects-v1-800x600-rects64-scene38398a5fd7c7aa8d006e66cd9db7fc7ecdfa2bd291d1267af5a384dde6092758` |
| viewport | 800×600 |
| warmups / samples | 5 / 300 |
| timing scope | draw-plus-submit-to-fence-p95 |
| p50 | 382,000 ns |
| p95 | 1,052,000 ns |
| max RSS | 30,556,160 bytes |
| GPU | Apple M4, vendor `106b`, device `1a040209` |
| backend | MoltenVK ICD `/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json` |
| ICD SHA-256 | `b514f51690582fb783383154b7a33c7816cc47e98ee1a1f652dccd3e996f0bf1` |
| fallback state | `none` |
| checksum | `10460147` (`sampled-u32-xor-stride-4096`) |
| retained / released bytes | 1,920,000 / 1,920,000 |
| timed full-frame upload / readback | 0 / 0 bytes |
| timed push-constant payload | 537,600 bytes (`300 × 64 × 28`) |
| capture | one post-timing capture, 1,920,000 bytes |
| admission | `measured-unadmitted` (`receipt-needs-common-admission`) |

The software/fallback state is explicitly `none`. The shared admission helper
rejects `software`, `unknown`, `unverified`, `synthetic`, and fallback GPU
identities; this row therefore cannot be admitted by relabeling a software
run.

## Bound artifacts and revisions

All paths below are relative to the clean PR worktree
`/tmp/simple-2d-web-renderer-gpu-pr-20260909`.

| Artifact | Path | SHA-256 |
|---|---|---|
| C source | `test/05_perf/bench/vulkan_2d_c/vk2d_bench.c` | `c988d2d9072d61faeef8facffc64755ae02a64ddc3f3e063e6ea4775fa221f9c` |
| scene source | `test/05_perf/bench/vulkan_2d_c/scenes.txt` | `26b4c4d9fe24aafba15f31b4547b2a6fabe2242421184358dd32c55d64ff4b51` |
| shader source | `test/05_perf/bench/vulkan_2d_c/rect.comp.glsl` | `5b5703ff722beef203a9c40c24ef3a26be937e0fb0780050054c505b33247b28` |
| compiled shader | `build/vulkan-2d-c-compare/rect.spv` | `785f4dc27b460b1a18dfe655a27890f4eb36fb75d12c59b721932c0eb240c2b7` |
| C binary | `build/vulkan-2d-c-compare/vk2d_bench` | `b881ab3569fd8ecb97a5a2864ba1e84c56d9a0361153c0b88a6dfa4a0596cfc3` |
| framebuffer capture | `build/vulkan-2d-c-compare/c-framebuffer.rgba` | `f7485b8db5e755a936810d7cfd2ce2c4fa8ce71cfc133e404a872340e1ded9f3` |
| raw C stdout | `build/vulkan-2d-c-compare/c.stdout.raw` | `91e1adf1a5a0d65e0c14474bbce00ea5266b60564a4fb3dcb1022df628e44eed` |
| raw C stderr | `build/vulkan-2d-c-compare/c.stderr.raw` | `63c7a8caf0bf3b1736f440619995dde2b9efbc96b6d4e5214de029a60e8cfc90` |
| runtime receipt | `build/vulkan-2d-c-compare/c.runtime.env` | `c_max_rss_bytes=30556160` plus raw-stream hashes |
| toolchain receipt | `build/vulkan-2d-c-compare/c.toolchain.env` | clang `179301dcb41ea78accc3fa0048a7e6f6710d891945a751a34addd622020c1818`; glslang `9bcd69d830b350aaa6e2254915ff74e46070e217b67f38daad27c1fc1f22910f` |
| C/comparator metadata row | `build/vulkan-2d-c-compare/c.env.raw` | generated projection inputs; not the complete producer stdout |
| projected C row | `build/vulkan-2d-c-compare/c.env` | generated admission projection |
| aggregate | `build/vulkan-2d-c-compare/evidence.env` | `compare_status=skipped` |

The worktree source revision at execution was `d543a6c0e4b` (the corrected
source/harness/test/report commit).

## Remaining admission gap

The C run has real device, artifact, raw-stream, toolchain, and RSS evidence,
but it has no `perf-binary-admission-v1` receipt. The row must remain
`measured-unadmitted` until a separately authorized admission step supplies a
C receipt and a newly measured, identically timed, admitted Simple row exists.
The common comparator therefore correctly records
`compare_status=skipped` and
`compare_reason=c-leg-measured-unadmitted:receipt-needs-common-admission`.
This report does not claim a C/Simple performance ratio.

## Corrected-run evidence

The corrected wrapper passes the committed scene table as a required input and
requires `scene_source=table`; the C fixture rejects an explicitly requested
missing or partial table. It retains producer stdout/stderr, records compiler
and shader-compiler identity/flags, captures macOS maximum RSS outside the GPU
timing interval, aligns the C sample boundary with Simple at
draw/record-through-fence completion, and destroys the bound buffer before
freeing its memory. The single canonical rerun produced all of the following:

- `c.stdout.raw` with `scene_source=table`, positive p50/p95, exactly 300 fence
  completions, at least 300 completion polls, and zero timed blocking Vulkan
  waits;
- `c.stderr.raw` with the required scene/capture diagnostics and macOS
  `/usr/bin/time -l` output;
- `c.runtime.env` with a positive maximum-RSS byte count and hashes binding
  both raw streams;
- `c.toolchain.env` with the exact C and shader compiler paths, SHA-256 values,
  versions, and flags;
- a 1,920,000-byte `c-framebuffer.rgba`, plus regenerated binary, SPIR-V,
  projection, and aggregate hashes bound to the corrected source revision.

Even after those checks, the C row remains `measured-unadmitted` and the
comparison remains `skipped` until authorized binary-admission receipts and a
matched admitted Simple row exist.
