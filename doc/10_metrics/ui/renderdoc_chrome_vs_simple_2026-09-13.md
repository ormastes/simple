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

**Corrected 2026-09-13 by live re-measurement. The earlier version of this table
reported `css-layout` at 3 submits / 3 readbacks and called it "a real open
finding, not a measurement gap". That was wrong**, and it was wrong in a
specific, avoidable way: the rows were hand-copied out of two 2026-09-12 lane
documents that span DIFFERENT configuration states and use WHOLE-RUN totals,
then read as if they were per-frame counts under the final configuration. The
`3` came from `web_catalog_vulkan_native_lane_macos_2026-09-12.md`, whose
`readback_pixels=2052000` is 3 x 684,000 — a PRE blur+glass cold measurement
that was never re-taken after the fix that took `overview` from 2 readbacks to
1. `css-layout` was fixed by the same change and simply never re-measured. The
ordering is on record, not inferred: the css-layout native-lane measurement
landed in `3fc7fb51292` (2026-09-12 13:42) and the device blur/glass batching
that collapsed the extra submits in `65634ae996a` (2026-09-12 18:35), five
hours later.

Measured live on this Mac, 2026-09-13, on the real Vulkan device, by the
official gate `scripts/check/check-web-vulkan-gpu-boundary-audit.shs` (which
arms `SIMPLE_VK_TIMING=1` and `SIMPLE_VK_ORDER_TRACE=1` itself and reads
per-frame counters drained at each frame boundary — the LAST, steady frame
decides the verdict). Interpreter binary
`/Users/ormastes/simple/build/cargo-r2/release/simple` (39,528,776 bytes,
2026-09-12 16:57), `SIMPLE_EXECUTION_MODE=interpreter`, 2 frames per run
(1 cold + 1 steady).

| page | resolution | verdict | submits/frame | readbacks/frame | dispatches/frame | host pixel loops |
|---|---|---|---|---|---|---|
| overview | 900x760 | PASS | 1 | 1 | 107 | 0 |
| css-layout | 900x760 | PASS | 1 | 1 | 287 | 0 |
| overview | 3840x2160 | PASS | 1 | 1 | 107 | 0 |
| css-layout | 3840x2160 | PASS | 1 | 1 | 297 | 0 |
| html, css-paint, animation, forms-media, tab-bar, evidence | — | not measured | not measured | not measured | not measured | not measured |

Independently cross-checked against the raw `SIMPLE_VK_ORDER_TRACE=1` event
stream, split on the `[audit-frame N]` markers rather than summed over the run.
Every one of the 8 frames (4 runs x cold + steady) carries exactly
`present=1`, `readback-entry=1`. Those trace events come from a different
emitter than the timing buckets, so they are a genuine second opinion and not a
restatement of the same counter. Per-frame `flush` counts are 5-6, which is NOT
a submit count: a flush with `pending_n=0` submits nothing and is deliberately
excluded (`gpu_boundary_audit.spl`, `audit_host_fallback_report`).

Commands that produced these (one per row):

```sh
SIMPLE_BIN=/Users/ormastes/simple/build/cargo-r2/release/simple \
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 \
  sh scripts/check/check-web-vulkan-gpu-boundary-audit.shs \
    --page examples/06_io/ui/web_catalog/css-layout.html --width 900 --height 760
```

Read against the invariants: **both pages satisfy 1 submit / 1 readback / 0 host
pixel loops at both sizes.** There is no open multi-submit finding on
`css-layout`.

Counting rule, so this class of error cannot recur: a "submits" or "readbacks"
figure in any document under `doc/10_metrics/ui/` is meaningless without the
frame count it covers. Quote per-frame numbers from the audit's own `classify`
output, never a run total divided or copied by hand. The
`--trace-derived` mode of `scripts/check/check-renderdoc-chrome-vs-simple.shs`
now delegates to exactly that parser, so the two tools cannot disagree again.

The pooled census fields `submits=` / `fences=` still read 0 against real
submits and must not be used; the gate reads the `sffi_submit_and_wait` timing
bucket instead, which measured `1 74 74` and `1 61 61` ms on the two
`css-layout` frames.

### The submit counter was under-wired, and now is not

Verifying the above surfaced a separate, real defect: `VK_T_SFFI_SUBMIT` — the
only submit counter this gate reads — was folded at exactly ONE of the seven
`vkQueueSubmit` call sites in `src/lib/gc_async_mut/gpu/engine2d`
(`backend_vulkan_helpers._flush_pending_compute_impl`). The font-atlas, packed-font,
resident-2d and immediate-dispatch paths all submitted uncounted, so a frame could
have reported `submits_per_frame=1` while performing several. Every submit now goes
through `vulkan_counted_submit_and_wait_fence`
(`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`), which counts by
construction. One raw submit is deliberately left unrouted and documented at the
facade: `VulkanSession.submit_and_wait` (`vulkan_session.spl`), because
`backend_vulkan` already imports `vulkan_session` and the reverse import would
close a module cycle. It has zero call sites repo-wide, so it contributes no
uncounted submit; if one is ever added, the counted door moves to a leaf module
both sides can import rather than the cycle being opened.

Proven live, not by fixture: with a second REAL queue submit spliced into the flush
path on this device, the gate answered
`FAIL — 2 frame(s) audited, violated: submits_per_frame=2 (>1)` (exit 1) and the
bucket read `sffi_submit_and_wait 2`. The sabotage was then reverted and the gate
returned to PASS with the bucket back at `1`. So the `<=1` verdicts above are
measured, not vacuous. Re-running `css-layout` at 900x760 **after** the counter fix
still reads 1 submit per frame — the previously-uncounted paths are not exercised by
these pages, so the fix is hardening and the verdicts stand unchanged.

Rendering is byte-unchanged by the refactor. Frame digests are identical before and
after the counter fix at every page and size: `743c2081` (css-layout 900x760),
`a15c50cd` (overview 900x760), `3c79ec0c` (css-layout 3840x2160), `5420e92d`
(overview 3840x2160) — and identical between the cold and steady frame within each
run.

Coverage is now enforced rather than remembered:
`check-web-vulkan-gpu-boundary-audit.shs --matrix` renders both pages at both sizes
and fails if any cell violates an invariant, so a per-page regression cannot sit
unobserved the way this one did. Measured on this host:
`PASS — 4 matrix cell(s) audited (overview + css-layout at 900x760 and 3840x2160), 0 violations`,
and the same four logs read back through the shared parser give
`RENDERDOC CHROME-VS-SIMPLE: PASS — 4 trace log(s) counted per frame, 0 invariant failures`
with `submits_per_frame=1` and `readbacks_per_frame=1` on every one.

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
