# Chrome vs Simple web renderer — RenderDoc-shaped GPU command comparison, 2026-09-13

Question: how many GPU-side commands does each renderer issue for the same catalog
page, and does the Simple side hold its GPU-offload invariants relative to Chrome.

**No RenderDoc capture exists, for either side, on any host — today included.** The
table below is therefore split into what was measured and what was not, and nothing
in it is presented as RenderDoc-derived when it is not.

Host census (2026-09-13, this Mac): Docker Desktop 29.2.1, server **linux/arm64**.
No colima, no lima, no orbstack, no ssh hosts, no `renderdoccmd` on the host.
RenderDoc has no macOS build, so the Mac itself can never capture.

## 1. Simple web renderer — TRACE-DERIVED, not RenderDoc-derived

Source: the GPU boundary audit and catalog lanes already in this repo
(`doc/10_metrics/ui/web_4k_showcase_gpu_boundary_audit_macos_2026-09-12.md`,
`web_catalog_vulkan_native_lane_macos_2026-09-12.md`). These come from the
renderer's own instrumentation, not from a graphics debugger.

| page | resolution | submits | readbacks | dispatches | backend draw ops | upload bytes | host pixel loops |
|---|---|---|---|---|---|---|---|
| overview | 900x760 (baseline) | 17 | 2 (5,472,000 B) | 107 | not measured (94 uploads/frame) | no counter | 16 |
| overview | 3840x2160 | 17 | 2 (66,355,200 B) | 107 | not measured (94 uploads/frame) | no counter | 16 |
| overview | 900x760, after device blur+glass | 1 | 1 (2,736,000 B) | 107 | 23 uploads/frame | no counter | 16 |
| overview | 900x760, `SIMPLE_VK_FONT_UPLOAD=u32` | **1** | **1** | 107 | 23 uploads/frame | ~60 MB/frame memcpy in the bytes lane | **0** |
| css-layout | 900x760, u32 font lane | **3** | not measured | not measured | not measured | `upload_ms` 184 -> 58 | 47 -> **0** |
| css-layout | 900x760, native readback (cold) | not measured | 3 (2,052,000 px) | not measured | 550 ops (rect_opaque 288, rect_alpha_blend 262, image 2) | not measured | not measured |
| css-layout | 300x253 | not measured | 1 | not measured | 187 ops | not measured | not measured |
| html, css-paint, animation, forms-media, tab-bar, evidence | — | not measured | not measured | not measured | not measured | not measured | not measured |

Also measured: `fence_waits` 17 -> 1, `cpu_fallback_count=0`,
`full_surface_composites=0`, `atlas_full_repacks` 5 -> 4 -> 0. The pooled census
reports `submits=0 fences=0` against 17 real submits and must not be used.

Commands that produced these:

```sh
SIMPLE_2D_BACKEND=vulkan SIMPLE_VK_READBACK=native SIMPLE_VK_IMAGE_UPLOAD=u32 \
SIMPLE_VK_RECT_UPLOAD=u32 SIMPLE_VK_FONT_UPLOAD=u32 \
  sh scripts/check/check-web-vulkan-gpu-boundary-audit.shs
```

Read against the invariants: `overview` in the final configuration satisfies
1 submit / 1 readback / 0 host pixel loops. **`css-layout` does not — 3 submits
against a limit of 1**, and that is a real open finding, not a measurement gap.

## 2. Chrome — NOT MEASURED

No column. Nothing in this repo has ever counted Chrome's draw calls, submits or
readbacks for these pages; the existing Chrome comparisons
(`chrome_vs_simple_catalog_diff_macos_2026-09-12.md`, the perf lane) measure wall
time and pixel geometry, which are not GPU command counts and must not be
substituted for them.

## 3. What was attempted today, and exactly where it stopped

Docker (linux/arm64) can supply the whole toolchain — verified, not assumed:

```
renderdoc            1.24+dfsg-1+deb12u1   arm64   available
chromium             152.0.7977.82         arm64   available
mesa-vulkan-drivers  22.3.6                arm64   available
```

An image was built from those packages (`simple-rdoc-lane:bookworm`, repo
bind-mounted read-only, never `COPY .`). Two blockers, both measured:

1. **Chromium under `renderdoccmd capture --wait-for-exit --opt-hook-children`
   never exits.** Two containers were abandoned still running at 600 s and at 23 min,
   with no `.rdc` written, and killed afterwards. Chromium's multi-process model plus
   RenderDoc's child hooking is the known-hard case here.
2. **Even unhooked, chromium in this container has no working GPU path.** The same
   command without RenderDoc completes in under 60 s and writes a screenshot, but
   logs `ContextResult::kTransientFailure: Failed to send
   GpuControl.CreateCommandBuffer` — it fell back to CPU rasterisation, so there
   would be no Vulkan work to capture even if the hook held.

CI is not an alternative today: every prior lane run either failed provisioning
(`34690832218`, `renderdoc_status=missing`), was cancelled with 0 steps, or was
never assigned a runner (`34692788301`, queued 42+ min).

The Simple side is blocked one step earlier still: there is no Linux Simple binary,
and the macOS seed cannot run the existing differ at all (see § 5).

## 4. What landed instead — the gate, runnable the moment a host exists

`scripts/check/check-renderdoc-chrome-vs-simple.shs`, backed by the pure-Simple
counter `src/app/ui/renderdoc_metrics/main.spl`. It counts, per page, draws /
dispatches / submits / readbacks / clears / pipeline switches / render targets /
events from a `renderdoc-events/v1` stream, and checks four invariants:

| invariant | bound |
|---|---|
| `simple_single_submit` | Simple presents <= 1 |
| `simple_single_readback` | Simple copies <= 1 |
| `simple_gpu_work_present` | Simple draws+dispatches > 0 |
| `simple_commands_within_2x_chrome` | Simple draws+dispatches <= 2x Chrome's |

Schema honesty: `presents` is the submit proxy and `copies` the readback proxy —
v1 has no submit or readback event type — and **upload bytes print `n/a`, never 0**,
because the schema cannot say. Host pixel loops are not observable in v1 at all;
that invariant stays with the boundary audit in § 1.

Verified on this Mac, against committed fixtures under `test/fixtures/renderdoc/`:

```
selftest ok   conforming -> rc=0 PASS — page conforming: 4 invariant(s) checked, 0 failed
selftest ok   violating  -> rc=1 FAIL — page violating: 2 of 4 invariant(s) failed
selftest ok   empty      -> rc=2 ERROR — nothing was checked (empty event stream: chrome=8 simple=0)
selftest ok   missing    -> rc=2 ERROR — nothing was checked (no such events file ...)
RENDERDOC CHROME-VS-SIMPLE: PASS — 4 selftest fixture(s) checked, 0 failed
```

and the honest refusal in full mode here:

```
RENDERDOC CHROME-VS-SIMPLE: ERROR — nothing was checked (renderdoccmd not found; run on the Linux lane)
```

An empty stream is ERROR rather than PASS on purpose: it satisfies every "at most
one" bound vacuously.

## 5. Found on the way: the existing differ cannot run on macOS

`check-renderdoc-web-diff.shs --selftest` reports "no Simple binary ... likely has
no 'run' subcommand". That diagnosis is wrong. The seed has `run`; the differ aborts
with **rc 138 (SIGBUS) and empty stdout** at JIT-compile time, on a cross-module
call. Bisected in
`doc/08_tracking/bug/renderdoc_seed_sigbus_cross_module_call_2026-09-13.md`. This is
why the new counter is a single module, and why its 8 alignment fixtures have never
actually been exercised on this host.

## 6. Unblocking, one command each

Chrome side, on any x86_64 Linux host with a real GPU (the arm64 software path
above is a dead end — chromium never reaches the GPU there):

```sh
sh scripts/check/check-renderdoc-chrome-vs-simple.shs
```

It self-tests first, then captures, exports and compares both sides, and prints the
per-page table. On a host without `renderdoccmd` it exits 2 rather than passing.

Simple side, still blocked on a Linux Simple binary — that is the single remaining
dependency for a real end-to-end verdict:

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh   # on the Linux lane host
```
