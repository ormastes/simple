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
samples, 800×600, 64 rectangles, a retained three-slot ring, and one
post-timing full-frame capture. The observed C stdout reported
`unconditional_submit_wait=false`, `timed_readback_bytes=0`,
`cpu_completion_wait_count=0`, and 300 fence completions through 924
nonblocking polls. That invocation predated the review fixes below and did not
retain its complete stdout stream, so those receipt-only fields are diagnostic
rather than filesystem-bound evidence.

Here, `cpu_completion_wait_count=0` means no timed blocking Vulkan wait call.
The submission thread still polls (with a short sleep) when it must reuse a
busy ring slot; the 924 poll count exposes that completion gating rather than
mislabeling it as fully independent CPU progress.

## Measured row

| Field | Value |
|---|---|
| workload | `vulkan-2d-c-rects-v1-800x600-rects64-scene485e33a5d8abd91eef7c9fb35497ab671177d6bbadae4e6abdd2b5cdc1ddbfc2` |
| viewport | 800×600 |
| warmups / samples | 5 / 300 |
| timing scope | submit-to-fence |
| p50 | 436,000 ns |
| p95 | 1,070,000 ns |
| max RSS | unavailable — the executed C harness did not capture process RSS |
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
| C source | `test/05_perf/bench/vulkan_2d_c/vk2d_bench.c` | `ff3fb3658db813c1aa29bc5d623587bb4ee783b7e76ee5bc3d55b4ba38f5883e` |
| scene source | `test/05_perf/bench/vulkan_2d_c/scenes.txt` | `26b4c4d9fe24aafba15f31b4547b2a6fabe2242421184358dd32c55d64ff4b51` |
| shader source | `test/05_perf/bench/vulkan_2d_c/rect.comp.glsl` | `5b5703ff722beef203a9c40c24ef3a26be937e0fb0780050054c505b33247b28` |
| compiled shader | `build/vulkan-2d-c-compare/rect.spv` | `785f4dc27b460b1a18dfe655a27890f4eb36fb75d12c59b721932c0eb240c2b7` |
| C binary | `build/vulkan-2d-c-compare/vk2d_bench` | `24f923437e3de867b81b169a83f79910fdec1a07b2528d8e9418e01c8be67200` |
| framebuffer capture | `build/vulkan-2d-c-compare/c-framebuffer.rgba` | `f7485b8db5e755a936810d7cfd2ce2c4fa8ce71cfc133e404a872340e1ded9f3` |
| C/comparator metadata row | `build/vulkan-2d-c-compare/c.env.raw` | generated projection inputs; not the complete producer stdout |
| projected C row | `build/vulkan-2d-c-compare/c.env` | generated admission projection |
| aggregate | `build/vulkan-2d-c-compare/evidence.env` | `compare_status=skipped` |

The worktree source revision at execution was `cdd0218f94a544e4adf3c937b2cd813c695c7673`.

## Remaining admission gap

The C run has real device and artifact evidence, but it has no
`perf-binary-admission-v1` receipt and the harness has no max-RSS observation.
Neither value can be reconstructed from the retained files without a new
measurement/admission action. The exact compiler flags are recoverable from
the executed wrapper revision, but compiler executable hashes/versions were
not retained at execution and therefore are also not admission evidence. The
retained pre-review C and Simple projections also use different timing scopes
(`submit-to-fence-p95` versus
`draw-plus-submit-to-fence-p95`), which the common admission helper correctly
rejects. The row must remain diagnostic until a separately authorized
admission step supplies a C receipt and a newly measured, identically timed,
admitted Simple row exists. This report does not claim a C/Simple performance
ratio.

## Review corrections after the measurement

The review found that the executed wrapper ran from its build directory
without explicitly binding `VK2D_SCENES`. For this exact default 800×600 run,
an independent row-by-row check proved that all 64 generated rectangles equal
the 64 committed table rows, so the measured pixels still represent the named
scene. The executed receipt nevertheless did not prove that it consumed that
artifact. The wrapper now passes the committed table as a required input and
requires `scene_source=table`; the C fixture rejects an explicitly requested
missing or partial table.

The wrapper now retains future producer stdout/stderr, records compiler and
shader-compiler identity/flags, captures macOS maximum RSS outside the GPU
timing interval, and aligns the C sample boundary with Simple at
draw/record-through-fence completion. The C fixture also destroys the bound
buffer before freeing its memory. These prospective corrections change the
source revision and timing method, so the existing binary and row intentionally
remain `measured-unadmitted`; they must not be relabeled as evidence from the
corrected source.

## Corrected rerun contract (not yet executed)

Cycle-2 static review passed shell syntax, C99 syntax, the focused source
contract, and diff hygiene without launching Vulkan. A future canonical rerun
must produce all of the following before its measured row can replace this
one:

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
