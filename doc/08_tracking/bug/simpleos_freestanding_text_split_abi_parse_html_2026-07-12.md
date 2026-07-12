# SimpleOS freestanding: text.split() ABI mismatch faults inside parse_html

**Date:** 2026-07-12 · **Status:** OPEN — root-caused; fix in-flight (peer's uncommitted `_html_split_on_lt`).

## Correction of an earlier overclaim

Commit `603fabe601` ("feat(os): SimpleOS WM boots real 4K … harness PASS") claimed the
`check-simpleos-wm-fullscreen-evidence.shs` harness PASSED at 4K. **That claim does not
reproduce and is withdrawn.** A clean `git worktree` checked out at exactly `603fabe601`,
built and run twice, FAILS 2/2 with byte-identical `reason=guest-render-fault`
(63 recoverable `[fault] EXCEPTION FRAME`, cr2=0). The single detailed PASS the authoring
run reported (baseline_ppm=24883217 bytes, changed_bytes=23174856, sha256 round-trip) was a
**heisenbug** — the underlying memory-corruption/ABI fault is nondeterministic (hang vs
garbage-completion vs occasional apparent success; adding `print` diagnostics changed the
outcome, a classic corruption signature). The committed evidence report correctly shows
`status=fail` today.

## Root cause (independent of 4K and of the allocator)

The freestanding target and the hosted runtime disagree on what `text.split()` returns —
whether an **encoded array handle** or the **decoded array pointer**. Inside
`parse_html` → `_html_scan_events` (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`),
`html.split("<")` hits this boundary and enters a recoverable-fault loop before
`parse_html` can complete — even for a 78-byte Browser Demo body. Serial log stalls
deterministically at `[simple-web-phase] phase=canonical-render-begin window=1` (a tiny
452×264 content window), then the harness gives up after its 60s readiness wait → empty
(0-byte) framebuffer capture.

This is NOT 4K-specific: it affects any HTML render on the freestanding target. 4K's WM
path is simply the first to exercise a live HTML content render at desktop-boot time, so it
is where the fault first became visible.

## What is / isn't affected

- Correct and kept: the 4K scanout config (3840×2160 argb8888 boots, scanout-evidence valid),
  the `rt_alloc`/`rt_alloc_zeroed` 16MB-truncation removal (verified byte-identical to the
  clamped version — NOT the cause), and `vgamem_mb=64`.
- Broken: the desktop's live HTML content render (the WM never becomes ready → 0-byte capture).

## Fix

A concurrent session landed (uncommitted, on disk, not yet on origin) `_html_split_on_lt`
replacing `html.split("<")` in `_html_scan_events`, with a comment describing exactly this
hosted-vs-freestanding split-return-type disagreement. Once that lands on origin and is
stable: re-run `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` **twice** and confirm
real PPM bytes reproducibly before any PASS claim. Do NOT re-assert 4K PASS on a single run.

## Follow-ups

- Freshly verify a lower-resolution fallback (e.g. 1024×768) is currently reliable before
  assuming it — the 07-11 report showed real 1024×768 pixels but for a different, unrelated
  failure reason, so it must be re-measured, not assumed.
- The generic `text.split()` ABI disagreement between hosted and freestanding runtimes is the
  real defect; the `_html_split_on_lt` workaround dodges it at one call site. A runtime-level
  fix (make `split` return the same representation in both lanes) would be the durable cure.
