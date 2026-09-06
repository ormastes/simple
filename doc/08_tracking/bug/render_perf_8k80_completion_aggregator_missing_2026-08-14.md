## 2026-08-17 Darwin ARM host closure

The parent aggregator remains implemented; the host-fixable gap was Darwin
portability in its own bounded contract matrix. The checker assumed GNU
`sha256sum`, GNU `sed -i`, and GNU `mv -T`, so its self-test failed on macOS
before it could validate any receipts. It now selects `sha256sum` or
`shasum -a 256`, rewrites fixtures through a portable temporary file, and
updates the `current` symlink with `ln -sfn`. The exact bounded positive and
deliberate-red matrix passes on macOS ARM64.

This host is an Apple M4 with Metal 4 and a 2880x1864 built-in display. It has
no NVIDIA runtime and cannot produce the NVIDIA Vulkan container receipt or a
7680x4320@80 physical-presentation receipt. Those live A4/A5/physical receipts
remain explicitly pending; no synthetic receipt was created.

## Triage 2026-08-17 — superseded host description

Blocker: unchanged and self-declared in this doc — the A7 aggregator is
IMPLEMENTED (`scripts/check/check-render-perf-8k80-container.shs`); what is
missing is live native A4 (CPU DrawIR) and A5 (strict Vulkan) receipts for the
same 7680x4320 workload. Requires the NVIDIA CUDA/Vulkan container host. Nothing
to fix in source.
# Render performance 8K80 parent aggregator is missing

Status: **IMPLEMENTED / LIVE EVIDENCE BLOCKED**

The canonical plan's A7 row requires one parent-authoritative decision over
the production-native CPU DrawIR receipt, strict Vulkan semantic-producer
receipt, and optional physical-presentation receipt. No
The `scripts/check/check-render-perf-8k80-container.shs` owner now exists; its
bounded positive and deliberate-red contract test passes. Live correlation is
still blocked by the admitted native A4/A5 artifacts, so
separate green rows could otherwise be combined manually or promoted despite
mismatched viewport, damage class, revision, device, or artifact provenance.

## Location and effect

- Plan contract: `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md`,
  A7 in §0-B.
- Research/design: `doc/01_research/local/render_8k80_container_gpu_completion.md`
  and `doc/04_architecture/render_8k80_container_gpu_completion.md`.
- Canonical Todo owner: TODO811.
- Implementation: `scripts/check/check-render-perf-8k80-container.shs`.
- Blocked acceptance: A7 and umbrella 8K80 promotion.

## Unblock condition

Run the implemented wrapper with explicit DrawIR, producer, optional physical,
and report inputs. It must correlate the CPU-native A4 and strict Vulkan A5
receipts for the same 7680x4320 workload, damage class, revision, and artifact
provenance; require p95 at most 12.5 ms, nonzero RSS/checksum, exact readback
scope, no disallowed fallback, and known completion; and reject missing,
duplicate, unknown, stale, or mismatched fields. A valid A4+A5 result without
physical evidence publishes `blocked-physical`. Only a fresh correlated
TODO684/TODO685 receipt can promote full PASS.

The bounded self-test matrix specified by TODO811 includes software-only
`blocked-physical`, physical promotion, and deliberate-red malformed,
mismatched, fallback, unknown-completion, zero-metric, timed-readback, and
over-budget rows.

Retain the generated aggregate plus every correlated input receipt. Owner:
render-performance integration. Final reviewer: independent highest-capability
Codex.

---

## 2026-08-17 — the stated blocker is FALSE: the NVIDIA container GPU host EXISTS and works

The triage note at the top of this file ("Requires the NVIDIA CUDA/Vulkan
container host") was re-verified today and is **not true of this host**. Measured
probes:

```
$ nvidia-smi --query-gpu=name,memory.total,driver_version --format=csv
NVIDIA RTX A6000, 49140 MiB, 580.126.16
NVIDIA TITAN RTX, 24576 MiB, 580.126.16

$ nvidia-container-cli info | head
NVRM version:   580.126.16
CUDA version:   13.0
Device Index:   0   Model: NVIDIA RTX A6000   Brand: NvidiaRTX
GPU UUID:       GPU-00833ff2-9a6b-95fa-66ce-2e1c96090b11

$ docker info --format '{{.ServerVersion}}'
29.1.3
$ ls /var/run/cdi/
nvidia.yaml

$ docker run --rm --gpus all ubuntu:24.04 sh -c 'ls /dev/nvidia*'   # rc=0
/dev/nvidia-uvm  /dev/nvidia-uvm-tools  /dev/nvidia0  /dev/nvidia1
```

GPU passthrough into a container works end to end today (CDI-based, exit 0, both
device nodes visible inside the container). `tools/docker/Dockerfile.render-8k80-nvidia`
and `scripts/setup/prepare-render-perf-8k80-container.shs` therefore have a
working host. **Any future triage deferring this bug as "needs a GPU container
host" is wrong and must not be re-recorded.**

### The real remaining blocker (recorded precisely, not as hardware)

What is still missing is purely *work*, not *hardware*: producing the live A4
(production-native CPU DrawIR, 7680x4320, 20 frames, damage 128,128,256,128) and
A5 (strict Vulkan semantic-producer, warmup 1 + 60 samples, 62 submits/62 fences,
device_readback oracle, p95 <= 12,500,000 ns) receipts requires a full compiler
build inside the container plus two long benchmark runs, then correlation through
`scripts/check/check-render-perf-8k80-container.shs`. That was not attempted in
this session because the host is currently running a stage-3 self-host build and
the session is limited to one concurrent test process; a 2 GiB-RSS 8K benchmark
run alongside it is exactly the contention that produced the empty timing receipt
recorded in `vulkan_8k_jit_retained_host_buf_sample_crash_2026-08-12.md`.

Status: **IMPLEMENTED / LIVE EVIDENCE PENDING — capacity-gated, not hardware-gated.**
