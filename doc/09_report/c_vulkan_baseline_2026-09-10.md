# C Vulkan 2D baseline — 2026-09-10

## Verdict

`fresh-candidate-measured-unadmitted; comparison-skipped; audit-warn`. This is
the C/reference side of the canonical `vulkan_2d_c` showcase only. The first
authorized measurement was recorded, but a later accidental invocation
overwrote the shared ignored output paths. That historical row remains
unverified for performance admission. A subsequent no-clobber run is retained
below as a fresh candidate. A later finalized-provenance invocation mistakenly
reused that producer ID after quarantining the prior directory; its distinct
durable evidence ID and collision audit are also retained below. Neither row
is admitted or constitutes a C/Simple/Chrome comparison.
No Simple bootstrap, Simple renderer run, Chrome builder, or cross-renderer
ratio was run in the authorized task. Its comparator result was
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

The authorized script's live contract was five untimed warmups, 300 timed
samples, 800×600, 64 rectangles loaded from the committed table, a retained
three-slot ring, and one post-timing full-frame capture. It initially retained
complete producer streams and reported
`unconditional_submit_wait=false`, `timed_readback_bytes=0`,
`cpu_completion_wait_count=0`, and 300 fence completions through 865
nonblocking polls. The canonical ignored files no longer hold that run. The
exact first-run stdout and stderr bytes were recovered from the timestamped
execution transcript and preserved in tracked report assets; their SHA-256
values exactly match the hashes recorded before the overwrite.

Here, `cpu_completion_wait_count=0` means no timed blocking Vulkan wait call.
The submission thread still polls (with a short sleep) when it must reuse a
busy ring slot; the 865 poll count exposes that completion gating rather than
mislabeling it as fully independent CPU progress.

## Historical authorized row

This row is preserved for incident history. It is stale at the canonical
`build/vulkan-2d-c-compare` paths and must not be consumed as live comparison
evidence.

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
| admission | `measured-unadmitted`; live artifact paths stale |

The software/fallback state is explicitly `none`. The shared admission helper
rejects `software`, `unknown`, `unverified`, `synthetic`, and fallback GPU
identities; this row therefore cannot be admitted by relabeling a software
run.

## Forensic bindings and current state

All paths below are relative to the clean PR worktree
`/tmp/simple-2d-web-renderer-gpu-pr-20260909`.

| Artifact | Path | SHA-256 |
|---|---|---|
| C source | `test/05_perf/bench/vulkan_2d_c/vk2d_bench.c` | `c988d2d9072d61faeef8facffc64755ae02a64ddc3f3e063e6ea4775fa221f9c` |
| scene source | `test/05_perf/bench/vulkan_2d_c/scenes.txt` | `26b4c4d9fe24aafba15f31b4547b2a6fabe2242421184358dd32c55d64ff4b51` |
| shader source | `test/05_perf/bench/vulkan_2d_c/rect.comp.glsl` | `5b5703ff722beef203a9c40c24ef3a26be937e0fb0780050054c505b33247b28` |
| compiled shader | `build/vulkan-2d-c-compare/rect.spv` | same hash in both runs: `785f4dc27b460b1a18dfe655a27890f4eb36fb75d12c59b721932c0eb240c2b7`; cannot identify one run |
| C binary | `build/vulkan-2d-c-compare/vk2d_bench` | same hash in both runs: `b881ab3569fd8ecb97a5a2864ba1e84c56d9a0361153c0b88a6dfa4a0596cfc3`; cannot identify one run |
| framebuffer capture | `build/vulkan-2d-c-compare/c-framebuffer.rgba` | same deterministic hash in both runs: `f7485b8db5e755a936810d7cfd2ce2c4fa8ce71cfc133e404a872340e1ded9f3`; canonical file was still overwritten |
| recovered authorized stdout | `doc/09_report/assets/c_vulkan_baseline_authorized_stdout_2026-09-10.raw` | `91e1adf1a5a0d65e0c14474bbce00ea5266b60564a4fb3dcb1022df628e44eed` |
| recovered authorized stderr | `doc/09_report/assets/c_vulkan_baseline_authorized_stderr_2026-09-10.raw` | `63c7a8caf0bf3b1736f440619995dde2b9efbc96b6d4e5214de029a60e8cfc90` |
| live raw C stdout | `build/vulkan-2d-c-compare/c.stdout.raw` | overwritten: `70a792dccab0288dfda9ced7c4fa08deb5525d8b2278661c1498945a6425098d` |
| live raw C stderr | `build/vulkan-2d-c-compare/c.stderr.raw` | overwritten: `4bf52da127f15009cd88be92142cac72668553999e0c02fb28c5b23c01a747f5` |
| live runtime receipt | `build/vulkan-2d-c-compare/c.runtime.env` | overwritten: `c_max_rss_bytes=30457856` plus second-run stream hashes |
| toolchain receipt | `build/vulkan-2d-c-compare/c.toolchain.env` | regenerated but stable: clang `179301dcb41ea78accc3fa0048a7e6f6710d891945a751a34addd622020c1818`; glslang `9bcd69d830b350aaa6e2254915ff74e46070e217b67f38daad27c1fc1f22910f` |
| live C/comparator rows | `build/vulkan-2d-c-compare/c.env.raw`, `c.env`, `simple.env`, `evidence.env` | overwritten by the accidental invocation |

The worktree source revision at both executions was `d543a6c0e4b` (the
corrected source/harness/test/report commit).

## Overwrite incident audit

The authorized run completed at `2026-09-10T05:22:12+09:00`; commit
`d543a6c0e4b` was created at `05:22:06+09:00`, and the corrected report commit
`5c967e19f8c` at `05:23:34+09:00`. The current ignored artifacts all have
modification times of `05:34:35` or `05:34:36+09:00`, after both commits. The
PR body update completed at `05:35:18+09:00`.

The wrapper proves that every live invocation targets the same output
directory. It removes the prior framebuffer/stdout/stderr and then replaces
the runtime, toolchain, projection, and aggregate files with shell
redirections or `tee`. The current producer stream reports p50 `388000` ns,
p95 `1058000` ns, RSS `30457856` bytes, and 871 completion polls, rather than
the authorized row's p50 `382000` ns, p95 `1052000` ns, RSS `30556160` bytes,
and 865 polls. Therefore the second invocation conclusively overwrote the
first live receipt set.

The local Codex rollout transcript named
`rollout-2026-09-10T05-21-52-01a087d5-8605-75f1-9c77-64176179e9da.jsonl`
retained the authorized command result at `2026-09-09T20:22:12Z` and a display
of the then-live raw streams at `20:22:28Z`. Reconstructing those two streams
byte-for-byte produces the exact pre-incident hashes recorded in commit
`5c967e19f8c`; the recovered tracked assets above preserve them. The original
ignored projection/runtime files were not preserved byte-for-byte and remain
stale/unverified at their canonical paths.

Prevention: never place Markdown containing backticks inside a double-quoted
shell assignment or command substitution used to update a PR. Write the body
as a literal file and pass `gh pr edit --body-file <path>`, or use an API field
that accepts the body directly. Do not use backtick or `$()` interpolation for
PR bodies.

## Remaining admission gap

The recovered first-run streams preserve real device and RSS observations,
but the canonical live receipt set is stale and there is no
`perf-binary-admission-v1` receipt. The row must remain historical and
unadmitted until a separately authorized measurement/admission step writes an
immutable per-run evidence directory and a newly measured, identically timed,
admitted Simple row exists.
The common comparator therefore correctly records
`compare_status=skipped` and
`compare_reason=c-leg-measured-unadmitted:receipt-needs-common-admission`.
This report does not claim a C/Simple performance ratio.

## Authorized-run evidence retained after the incident

The corrected wrapper passes the committed scene table as a required input and
requires `scene_source=table`; the C fixture rejects an explicitly requested
missing or partial table. It retains producer stdout/stderr, records compiler
and shader-compiler identity/flags, captures macOS maximum RSS outside the GPU
timing interval, aligns the C sample boundary with Simple at
draw/record-through-fence completion, and destroys the bound buffer before
freeing its memory. The single authorized rerun initially produced all of the
following. After the incident, only the reconstructed raw streams, committed
report values, and stable source/toolchain hashes remain attributable to that
first rerun:

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

## Fresh immutable run — `c-m4-moltenvk-20260910-01`

This section records the one authorized live invocation performed after the
immutable-run protocol was installed. The preflight checked that the run ID
did not exist, inspected the supported `VK2D_RUN_ID` interface without
invoking workload help, and validated the script with `sh -n`. No second live
invocation was made in that original authorized step.

Exact command:

```text
VK2D_RUN_ID=c-m4-moltenvk-20260910-01 sh scripts/check/check-vulkan-2d-c-compare.shs
```

The producer receipt was originally published at the manifest path below. It
was created with mode `0700`; its regular files were mode `0644` except for the
captured native benchmark (`0755`). Every file had link count one and no entry
was a symlink. Before the later finalized-provenance invocation, this complete
directory was moved to
`build/vulkan-2d-c-compare/runs/.quarantine-c-m4-moltenvk-20260910-01-pre-finalized/`.
The later run now occupies the original producer path, so that path must not be
used to resolve this older row. The producer's `latest` file is a convenience
pointer with `authoritative=false` and is not used as evidence input.

That ignored build directory is not durable PR evidence: it is omitted from
Git, remains owner-writable, and may disappear during cleanup. Exact text
receipts were therefore copied byte-for-byte to the tracked asset directory
`doc/09_report/assets/c-m4-moltenvk-20260910-01/`. The 1,920,000-byte
framebuffer, 37,832-byte native binary, and 2,336-byte SPIR-V binary were not
duplicated; the tracked manifest and framebuffer hash receipt preserve their
observed SHA-256 identities. These are candidate receipts, not an admission
receipt.

| Item | Value |
|---|---|
| retained run manifest | `build/vulkan-2d-c-compare/runs/.quarantine-c-m4-moltenvk-20260910-01-pre-finalized/run.manifest.env` |
| manifest schema | `immutable-vulkan-2d-c-run-v1` |
| config SHA-256 | `0cbc4bd07a7ce7c067a714adf0f393f2261d867405eef617b5925eeeec4f99b2` |
| fixture SHA-256 | `26b4c4d9fe24aafba15f31b4547b2a6fabe2242421184358dd32c55d64ff4b51` |
| C source SHA-256 | `c988d2d9072d61faeef8facffc64755ae02a64ddc3f3e063e6ea4775fa221f9c` |
| shader source SHA-256 | `5b5703ff722beef203a9c40c24ef3a26be937e0fb0780050054c505b33247b28` |
| shader binary SHA-256 | `785f4dc27b460b1a18dfe655a27890f4eb36fb75d12c59b721932c0eb240c2b7` |
| C binary SHA-256 | `b881ab3569fd8ecb97a5a2864ba1e84c56d9a0361153c0b88a6dfa4a0596cfc3` |
| ICD SHA-256 | `b514f51690582fb783383154b7a33c7816cc47e98ee1a1f652dccd3e996f0bf1` |

### Measured C row (unadmitted)

The C workload used 800×600, five warmups, 300 timed samples, 64 table
rectangles, a three-slot ring, and one post-timing full-frame capture. Timing
scope is draw-plus-submit-to-fence. The GPU identity was Apple M4 (vendor
`106b`, device `1a040209`) through the MoltenVK ICD. No software fallback was
detected.

| Metric | Value |
|---|---|
| p50 / p95 | `438000 / 1023000 ns` |
| max RSS | `30801920 bytes` |
| completion polls / fence completions | `920 / 300` |
| timed blocking `vkWaitForFences` calls | `0` |
| synchronous fence-status polls | `920` |
| timed full-frame upload / readback | `0 / 0 bytes` |
| upload bytes | `537600` |
| retained / released bytes | `1920000 / 1920000` |
| capture bytes | `1920000` |
| capture checksum | `10460147` (`sampled-u32-xor-stride-4096`) |
| event generations / damage pixels | `300 / 144000000` |
| C status | `measured-unadmitted` (`receipt-needs-common-admission`) |

### Durable candidate artifact bindings

All paths are relative to the clean PR worktree
`/tmp/simple-2d-web-renderer-gpu-pr-20260909`.

| Artifact | Tracked candidate path | SHA-256 |
|---|---|---|
| run manifest | `doc/09_report/assets/c-m4-moltenvk-20260910-01/run.manifest.env` | `513a99c079ad5b826f978d18e98055b3920e36953cdc0c4a5ea26c3372893bed` |
| raw C stdout | `doc/09_report/assets/c-m4-moltenvk-20260910-01/c.stdout.raw` | `0fd46e39bea7093857f48b3267b7b52a78b11c9dedadc66f616b87cb2f2925ea` |
| raw C stderr | `doc/09_report/assets/c-m4-moltenvk-20260910-01/c.stderr.raw` | `032b4fbd699149eba53141ddace305d4e8f8a5281eef46c279125e7f52c0173a` |
| C runtime receipt | `doc/09_report/assets/c-m4-moltenvk-20260910-01/c.runtime.env` | `ff49d3c64665a014480e8ef4c512b97aacba44d8da81b095934d353e2f86642c` |
| C toolchain receipt | `doc/09_report/assets/c-m4-moltenvk-20260910-01/c.toolchain.env` | `df0ad35d0d5ac72724be83c1555e0dc488546fc1a858f788212129304e959619` |
| C row | `doc/09_report/assets/c-m4-moltenvk-20260910-01/c.env` | `390917cca45cd4848b249a0bca691df218196fefd5913b87fc40a8130a11de44` |
| combined raw row | `doc/09_report/assets/c-m4-moltenvk-20260910-01/c.env.raw` | `6bdeecd21ad7454477652a92a3d7c1c8db9cbfae4ba3af460516e55b9fa8af75` |
| skipped Simple row | `doc/09_report/assets/c-m4-moltenvk-20260910-01/simple.env` | `9efd5dffcd4bb8ffbf90c7b560fdf2975c2cd7605482f8a49fd91129684f56e0` |
| skipped Simple runtime receipt | `doc/09_report/assets/c-m4-moltenvk-20260910-01/simple.runtime.env` | `30b727e147526d10a5762f2177be947f865becd37cd59df2753fcc83cdf9237c` |
| aggregate evidence | `doc/09_report/assets/c-m4-moltenvk-20260910-01/evidence.env` | `4a5f04d67e520eb78af3a534eb911804a8a45b00f8d3da06606d56789ba178af` |
| framebuffer hash receipt | `doc/09_report/assets/c-m4-moltenvk-20260910-01/c-framebuffer.rgba.sha256` | `ee25bc8fded5ec2ab95072d3ec862ca993071a2b8a2d9ccd40963f9e82cb04a1` |

The framebuffer was independently checked as exactly 1,920,000 bytes. Folding
little-endian `u32` values at stride 4096 reproduced checksum `10460147`; its
full SHA-256 reproduced
`f7485b8db5e755a936810d7cfd2ce2c4fa8ce71cfc133e404a872340e1ded9f3`.

### Audit limitations

Filesystem birth/modification times place production and publication between
`2026-09-10T06:34:45+09:00` and `06:34:46+09:00`. They are observation-only:
the manifest does not carry producer start/end timestamps, a repository commit,
or the wrapper's own hash. The current source, scene, shader, and wrapper match
HEAD `2fb1deeb75b4c77855afd973a656565aa2fadc95`, while the corrected C
source/evidence contract entered in
`d543a6c0e4bcfa8a1f7393cb616b0c7d656fd9d4` and the no-clobber protocol in
`2fb1deeb75b4c77855afd973a656565aa2fadc95`. This commit association is an
auditor observation, not a manifest-bound claim.

The raw value `cpu_completion_wait_count=0` proves only that the timed region
did not call blocking `vkWaitForFences`. `poll_fence_complete` synchronously
loops over `vkGetFenceStatus` and `nanosleep` until each reused/final ring slot
completes; the run reports 920 such polls. Therefore this candidate proves no
timed framebuffer readback and no unconditional Vulkan wait, but it does not
prove CPU-independent asynchronous progress or literally zero CPU waiting.

The Simple row is `skipped` with reason `bootstrap-seed-forbidden`; its raw
stdout/stderr are empty and its binary/artifact hashes are intentionally
empty. Consequently `compare_status=skipped`,
`compare_ratio_x1000=0`, and
`compare_reason=c-leg-measured-unadmitted:receipt-needs-common-admission`.
This fresh receipt is measured evidence only; it does not admit the C row or
claim C/Simple/Chrome parity. Audit status is `WARN`: values, hashes, modes,
scene/toolchain/binary/shader/ICD bindings, RSS, fallback, capture checksum,
retained/released bytes, and skipped aggregate are internally consistent, but
producer time/revision are not manifest-bound and the timed path performs
synchronous poll/sleep completion gating.

## Finalized-provenance receipt — `c-m4-moltenvk-provenance-20260910-01`

This is the durable evidence ID for one later current-protocol C invocation.
The producer was asked to use that ID but instead requested the already-used
producer ID `c-m4-moltenvk-20260910-01`. The earlier published directory was
manually quarantined and moved intact to
`build/vulkan-2d-c-compare/runs/.quarantine-c-m4-moltenvk-20260910-01-pre-finalized/`
before the new invocation. The current helper then reserved a private stage
and published the replacement atomically without overwriting that quarantine.
This preserved the old bytes, but moving the prior reservation defeated global
run-ID uniqueness. Therefore the producer ID disposition is `manual-quarantine`
and the colliding producer ID is not used as the durable tracked identity.

The quarantined copies of all ten corresponding text receipts match the
already-tracked `doc/09_report/assets/c-m4-moltenvk-20260910-01/` files
byte-for-byte. Its 1,920,000-byte framebuffer also reproduces the prior
tracked framebuffer hash. Those old tracked assets were not changed. The new
receipts are copied byte-for-byte under the distinct durable ID
`doc/09_report/assets/c-m4-moltenvk-provenance-20260910-01/`.

The exact producer command was:

```text
VK2D_RUN_ID=c-m4-moltenvk-20260910-01 sh scripts/check/check-vulkan-2d-c-compare.shs
```

The retained stdout has exactly one workload result line, the retained stderr
has exactly one framebuffer-dump line and one `/usr/bin/time -l` block, and
the result line declares five warmups and 300 samples. This proves that this
receipt set contains one benchmark-process execution. It cannot prove that no
unrelated invocation occurred outside this receipt set.

### Measured C row (unadmitted)

| Metric | Value |
|---|---|
| viewport / rectangles | `800×600 / 64` |
| warmups / samples | `5 / 300` |
| p50 / p95 | `446000 / 1047000 ns` |
| max RSS | `30605312 bytes` |
| completion polls / fence completions | `921 / 300` |
| timed blocking `vkWaitForFences` calls | `0` |
| synchronous fence-status polls | `921` |
| timed full-frame upload / readback | `0 / 0 bytes` |
| push-constant upload bytes | `537600` |
| retained / released bytes | `1920000 / 1920000` |
| capture bytes | `1920000` |
| capture checksum | `10460147` (`sampled-u32-xor-stride-4096`) |
| event generations / damage pixels | `300 / 144000000` |
| GPU / fallback | `Apple M4` through bound MoltenVK ICD / `none` |
| C status | `measured-unadmitted` (`receipt-needs-common-admission`) |

### Durable finalized-provenance bindings

| Artifact | Tracked candidate path | SHA-256 |
|---|---|---|
| run manifest | `doc/09_report/assets/c-m4-moltenvk-provenance-20260910-01/run.manifest.env` | `a850cb0fdc43958669246e69f36c7e6abbe317d7e3732cbb4ca06c747572ddef` |
| raw C stdout | `doc/09_report/assets/c-m4-moltenvk-provenance-20260910-01/c.stdout.raw` | `f31fc0be19df98222cdcc6feded38fad5cfaf50e392c607481fe5b1c203dcd62` |
| raw C stderr | `doc/09_report/assets/c-m4-moltenvk-provenance-20260910-01/c.stderr.raw` | `d03b1f08a1382f9e028307bd32bb55da3b16642a288f71a46fb7709c2aaba616` |
| C runtime receipt | `doc/09_report/assets/c-m4-moltenvk-provenance-20260910-01/c.runtime.env` | `c9b5a009ec00f26453bff72ef2869db18e7629938eae3bd1f161d42880ab2ed7` |
| C toolchain receipt | `doc/09_report/assets/c-m4-moltenvk-provenance-20260910-01/c.toolchain.env` | `df0ad35d0d5ac72724be83c1555e0dc488546fc1a858f788212129304e959619` |
| C row | `doc/09_report/assets/c-m4-moltenvk-provenance-20260910-01/c.env` | `49eefc288e621be96a93c606ed27a58fe441e139b4498deb5ba86c06881ccd2f` |
| combined raw row | `doc/09_report/assets/c-m4-moltenvk-provenance-20260910-01/c.env.raw` | `de0a00b5c625640e64ddbcd9dfa29163a7e8c72e7660081706f1b3ad136230e5` |
| skipped Simple row | `doc/09_report/assets/c-m4-moltenvk-provenance-20260910-01/simple.env` | `9efd5dffcd4bb8ffbf90c7b560fdf2975c2cd7605482f8a49fd91129684f56e0` |
| skipped Simple runtime receipt | `doc/09_report/assets/c-m4-moltenvk-provenance-20260910-01/simple.runtime.env` | `30b727e147526d10a5762f2177be947f865becd37cd59df2753fcc83cdf9237c` |
| aggregate evidence | `doc/09_report/assets/c-m4-moltenvk-provenance-20260910-01/evidence.env` | `4a5f04d67e520eb78af3a534eb911804a8a45b00f8d3da06606d56789ba178af` |
| framebuffer hash receipt | `doc/09_report/assets/c-m4-moltenvk-provenance-20260910-01/c-framebuffer.rgba.sha256` | `ee25bc8fded5ec2ab95072d3ec862ca993071a2b8a2d9ccd40963f9e82cb04a1` |
| quarantine/collision audit | `doc/09_report/assets/c-m4-moltenvk-provenance-20260910-01/quarantine.audit.env` | `72b248d086595212ec94c47796129890977b1d5b7a44bc0b4c0820269de3824c` |

The ignored producer directory remains
`build/vulkan-2d-c-compare/runs/c-m4-moltenvk-20260910-01/`, as recorded by
the immutable manifest. The tracked directory name does not rewrite the
producer manifest or its self-digest.

### Provenance and semantics audit

The manifest self-digest is
`a38d4562201fc594780716cd10084e079f9e32dd202f71c90c2c28af7fe7ee17`.
It binds clean commit `102af6a114abc7cc768a61b78bf5f7d5976839e7`, tree
`38876d339e6b497ea42400228e1327b2ff5fe347`, the empty tracked-diff hash,
start `2026-09-09T22:39:01Z`, and nonce
`1788993541-1631-64541-RyA16S`. The UTC timestamp exactly matches epoch
`1788993541`. Hash recomputation passed for the wrapper, immutable-run helper,
admission helper, C and Simple sources, scene, shader source and binary, C
binary, MoltenVK ICD, raw streams, runtime/toolchain receipts, projected rows,
and aggregate. The configuration hash and both newline-delimited argv hashes
also recompute exactly.

The live directory is mode `0700`, contains no symlinks, and every regular
file has link count one. Its benchmark is mode `0755`; the remaining files are
mode `0644`. The framebuffer is exactly 1,920,000 bytes with SHA-256
`f7485b8db5e755a936810d7cfd2ce2c4fa8ce71cfc133e404a872340e1ded9f3`;
folding little-endian `u32` values at stride 4096 reproduces checksum
`10460147`.

The timed path has no blocking `vkWaitForFences` call and no timed framebuffer
readback, but it synchronously performs 921 `vkGetFenceStatus` polls with
`nanosleep` when reusing and draining ring slots. The 921 poll/sleep operations
therefore do not prove
CPU-independent asynchronous progress or zero CPU waiting. The Simple row is
`skipped` with `bootstrap-seed-forbidden`; its streams are empty and its
binary/artifact hashes are intentionally empty. The aggregate correctly says
`compare_status=skipped`, `compare_ratio_x1000=0`, and
`compare_reason=c-leg-measured-unadmitted:receipt-needs-common-admission`.

Audit status is `WARN`, not `PASS`: all retained provenance, raw receipt,
metric, checksum, mode, and skip bindings are internally consistent, but the
producer ID collided with an earlier receipt, the C row lacks common binary
admission, the timed path has synchronous poll/sleep completion gating, and no
Simple or Chrome comparison was executed. Thus Simple and Chrome are both
explicitly skipped for this candidate.
