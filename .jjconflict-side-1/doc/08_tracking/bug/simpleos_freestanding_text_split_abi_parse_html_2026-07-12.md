# SimpleOS freestanding: text.split() ABI mismatch faults inside parse_html

**Date:** 2026-07-12 · **Status:** OPEN — split-ABI runtime bug FIXED (2026-07-13);
harness still blocked by a DEEPER, distinct codegen bug (see "Verified 2026-07-13").

## Verified 2026-07-13 — runtime split ABI fixed, but it was NOT the sole blocker

The `text.split()` freestanding bug is real and now fixed at the runtime level, but it
is **two** separate defects, and the deeper one is a cranelift codegen bug (unfixable in
`baremetal_stubs.c`):

1. **FIXED — return-representation mismatch (the actual "ABI mismatch").**
   `rt_string_split` (x86_64 `baremetal_stubs.c`) returned a **RAW** array pointer
   (`(RuntimeValue)(uintptr_t)DECODE_PTR(arr)`), but freestanding cranelift codegen
   inlines `.len()`/`[i]` on a split result assuming a **TAGGED** `ENCODE_PTR` heap
   handle (the representation a Simple-built `[text]` carries). With the raw pointer,
   `parts.len()` read garbage (`2305843009213693951`) and every `parts[i]` was `nil`.
   Fix: `return arr;` (the tagged handle from `rt_array_new`/`rt_array_push_handle`).
   Also fixed an internal bug: split passed `ENCODE_INT(idx)` to `rt_string_slice`,
   which treats its indices as RAW (like `rt_string_trim`) → shifted substrings; now
   passes raw. `rt_string_substr` had the same encoded-index bug (fixed too).
   Isolated probe (`examples/09_embedded/simple_os/arch/x86_64/text_ops_probe_entry.spl`
   + `scripts/os/text_ops_probe_run.shs`) PROVES it: `"<html><body>hi</body></html>"`
   → 5 correct parts on BOTH a rodata literal AND a heap-built string; `starts_with`,
   `char_at`, `index_of`, `substring` all correct on the heap string at shallow frame.

2. **STILL BLOCKING — but NOT in the string-runtime layer, and NOT parse_html.**
   Once split returns correct data, the 4K WM first-frame render still faults
   DETERMINISTICALLY (2/2 identical runs, `reason=guest-render-fault`, ~59-63 recoverable
   `[fault] EXCEPTION FRAME`), first fault right after the `[fat32-c]` mount marker, with
   no render/`simple-web` marker reached. The fault is inside `decode_string`
   (`movzbl (%rax)` at the `s->hdr.type` load) dereferencing a mis-decoded value of the
   form `0xNN00000000[01]` (e.g. `cr2=0x1f00000000`, `0x1400000001`). Location is
   deterministic; the frame *count* (59 vs 63) just reflects where QEMU was killed — not
   signal.

   **The "frame-depth codegen mis-decode" hypothesis was tested and DISPROVEN.** Isolated
   probes (all in `examples/09_embedded/simple_os/arch/x86_64/`, run via `scripts/os/*_run.shs`)
   reproduce parse_html's exact behavior on HEAP-built strings from a 12-frame-deep call
   stack with live spilled locals, and all PASS with no fault:
   - `text_scan_deep_probe_entry.spl`: split → `parts[k].starts_with`/`.index_of(">")`/
     `seg = seg + "<" + parts[k]` (concat)/`.substring`/`.char_at(0)`/`[""; cap]` init,
     PLUS the nested `[[text]]` return + `ev[0]`/`ev[1]` re-index → 12 correct events.
   - `parse_html_real_probe_entry.spl`: calls the REAL `parse_html`
     (`simple_web_layout_debug_attr_by_id`) → no fault.
   - `render_draw_ir_probe_entry.spl`: calls the REAL WM render entry
     `simple_web_layout_render_html_draw_ir` (parse_html + layout + draw-ir build) on a
     heap HTML string at depth → no fault.

   So the string char ops, nested arrays, parse_html, and the full simple-web render path
   are all CLEAN in isolation on heap-built text. The harness fault is in the WM/compositor
   FIRST-FRAME path (post-`[fat32-c]`-mount), NOT reproduced by rendering constant/heapified
   HTML — a data-flow specific to boot (candidate: the fat32 background-manifest read +
   `_motion_manifest_lines`/`parse_i64` in `src/os/compositor/background_motion_provider.spl`,
   or WM window-scene assembly) hands a mis-tagged value to a string op. `_fat32_read_file_text_value`
   itself returns a correctly-tagged `rt_string_from_cstr` string, so the fat32 text read is
   NOT the culprit. ROOT CAUSE OF THE HARNESS FAULT IS UNRESOLVED and is outside the
   string-runtime cluster fixed here.

   Discriminator proof (single runs): reverting ONLY `rt_string_to_int` to the stub →
   fault UNCHANGED (to_int innocent). Reverting `rt_string_split` back to the raw return →
   fault GONE but the boot enters an infinite `[heap] alloc` loop (code spinning on garbage
   split data), still never rendering. So the correct split fix *surfaces* the downstream
   fault; neither state greens the harness.

**Bottom line:** the runtime split/substr/to_int fixes are correct and land (probe-proven),
and plain `html.split("<")` now works at the runtime layer (peer `_html_split_on_lt` byte
workaround no longer needed for `split` itself). The 4K harness remains RED, blocked by a
DISTINCT, still-unresolved fault in the WM/compositor first-frame boot path — NOT a
string-runtime bug and NOT reproduced by parse_html/render on heap HTML in isolation. Do NOT
claim 4K PASS until that separate fault is root-caused.

---

### Original report (2026-07-12)

**Status:** OPEN — root-caused; fix in-flight (peer's uncommitted `_html_split_on_lt`).

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
