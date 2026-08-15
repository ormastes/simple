# `GLYPH_RGB_SHA256=pending` is not the first blocker for showcase cells 4/5/6

**Status:** OPEN — ARCHITECTURAL. no legitimate calibration value exists yet,
and none was invented.

**Re-checked 2026-08-09:** `GLYPH_RGB_SHA256=pending` is still line 18 of the
gate script; still the last blocker in the chain described below. Calibrating
it for real requires the full chain this doc lays out — a clean dedicated
worktree, a quiet host, an `native-build` closure of the hosted-WM entry
point, and a live X11 window capture to hash — none of which fits in an
interpreter-only, no-native-build-closure verification pass. Deferred rather
than attempted with a shortcut; a shortcut here (guessing/back-filling the
hash) is explicitly the thing this doc already warns against. No code change
made this pass; characterization confirmed accurate as written below.
**Gate:** `scripts/check/check-linux-hosted-wm-live-window-evidence.shs:18`
**Investigated:** 2026-08-01, host `linux-x86_64`, base
`f7bfaf973de2a2c398fec7f11ea4235e19f557ab`, re-checked against
`55115a82411a596449060679a8c837cc63c48c01`. The gate script is byte-identical
between those two revisions, so every finding below still applies at the
current tip.

## Summary

`GLYPH_RGB_SHA256=pending` makes the gate hard-fail with
`glyph-oracle-pending-calibration-required-<sha>` (line 968). That is real,
but it is the **last** blocker in the chain, not the first. Three earlier
blockers were found, two of them structural:

| # | Blocker | State |
|---|---|---|
| 1 | Gate had never once reached the capture stage | PROVED |
| 2 | Hosted entry closure did not parse with any compiler | FIXED (this session) |
| 3 | `native-build` per-file 60s timeout vs. host load | ENVIRONMENTAL, open |
| 4 | `JsValue.Symbol` used but not declared in the imported enum | OPEN |
| 5 | `GLYPH_RGB_SHA256=pending` | OPEN — needs a real render |

## The other capture report is not this gate

`doc/09_report/hosted_wm_capture_evidence_2026-08-01.md` (landed
`55115a82411`) is a **different, much weaker** probe: a 16x16 buffer,
`backend_selected=simple_web_request_local_raster_readback`,
`production_admission: fail`, and `reason: runtime-rust-seed-forbidden`. It
carries no glyph crop and no glyph hash, and must not be mistaken for a
capture from this gate. Worth noting that it classifies `bin/simple` as
`simple_bin_status: forbidden` — the pure-Simple provenance of the deployed
binary is itself contested, whereas this gate's check (line 597-602, a
`--version` substring match on `rust-built`/`rust seed`/`bootstrap seed`)
lets `simple-bootstrap 1.0.0-beta` through. The two admission rules
disagree; that disagreement should be resolved before any pin is trusted.

## Blocker 1 — the gate has never reached a capture (PROVED)

The only evidence artefact on this host,
`build/linux-hosted-wm-live-window-evidence/evidence.env` (2026-07-30),
reads:

```
linux_hosted_wm_live_window_status=fail
linux_hosted_wm_live_window_reason=source-provenance-unavailable
linux_hosted_wm_live_window_glyph_crop_sha256=
```

`glyph_crop_sha256` is **empty**, and `simple_bin_sha256` is empty too — the
run died at `resolve_source_provenance` before a compiler was even
selected. `git_dependency_tree_clean` (line 213) requires `src/os` and
`src/lib` to be clean, and the shared working copy never is. **Any
calibration attempt must run from a clean checkout**, e.g. a dedicated
worktree; that alone gets past blocker 1.

## Blocker 2 — the closure did not parse (FIXED)

See
`doc/08_tracking/bug/hosted_wm_entry_closure_unparseable_grammar_gaps_2026-08-01.md`.
Four landed source sites were rejected by both the pure-Simple front end
and the Rust seed, so `native-build` aborted during discovery and no
artefact could exist. Repaired; the closure now reaches code generation.

## Blocker 3 — per-file compile timeout under host load

`simple native-build` has `--timeout <secs>` (default **60**) per file. The
gate invokes `native-build` without that flag, so it always gets 60s. On a
host at load average ~140 (32 cores, other sessions), 89–96 files of the
closure exceed 60s each and the build aborts with
`native-build aborted: N file(s) failed to compile`. Files as small as 136
lines (`src/lib/common/io/async_traits.spl`) timed out — this is
contention, not file complexity.

This is not a reason to weaken the gate. It is a reason to run the gate on
a quiet host. Recorded so the failure is not misread as a compiler defect.

## Blocker 4 — `JsValue.Symbol` is used but not declared (PROVED)

With a 900s per-file budget the closure got far enough to surface a real
code-generation failure:

```
src/lib/nogc_sync_mut/js/engine/interpreter.spl:
  mir: Unsupported HIR construct: unknown variant or method 'Symbol' on enum JsValue
```

`interpreter.spl:126` both matches and constructs `JsValue.Symbol(id)`:

```
                JsValue.Symbol(id): return JsValue.Symbol(id: id)
```

but line 7 imports `use std.js.types.js_types.JsValue`, and there are
**three** divergent `JsValue` enums in the tree:

| File | Has `Symbol`? |
|---|---|
| `src/lib/js/types/js_types.spl` (what `std.js.types` resolves to) | **NO** |
| `src/lib/nogc_sync_mut/js/types/js_types.spl` | **NO** |
| `src/lib/common/js/types/js_types.spl` | YES — `Symbol(id: i64)` |

`interpreter_async.spl:654` has the same problem. Either the import is
wrong or the two other enums are missing the variant; picking between them
needs the JS-engine owner, so it is filed rather than guessed at here. This
blocks the hosted-WM closure independently of host load.

## Blocker 5 — the calibration itself

**No value has been pinned.** A hash invented, guessed, or back-filled to
turn the gate green would be worse than leaving it pending — see
`doc/.../reference_fabricated_crypto_test_vector_in_bip39_kat` for the
precedent this repo already has.

### What the oracle actually measures

Line 962-965 crops **60x18 at +122+82** out of the 1024x720 production
framebuffer and out of the live X11 window screenshot, and requires:

1. `glyph_sha == GLYPH_RGB_SHA256` (the pin), and
2. the two crops to be **byte-identical** (`live_glyph_match`), and
3. a deliberate one-byte corruption of the crop to change the hash
   (`calibration_status`, line 974-977).

The crop region is the "Terminal" window title. `hosted_entry.spl:184-196`
creates that window at x=58, y=76, and the gate's own comment fixes the
title at +66,+8 — i.e. text origin (124, 84), crop starting two pixels up
and left.

### Valid calibration procedure

1. Fresh clean checkout (worktree), so `git_dependency_tree_clean` passes.
2. Quiet host, so every file compiles inside the gate's 60s budget.
3. Run the gate with `LINUX_HOSTED_WM_CALIBRATE_GLYPH=1`. That is the
   designed calibration path: `glyph_oracle_mode` returns `calibration-only`,
   the pending hard-fail is skipped, the whole pipeline runs, and the run
   ends at `glyph-oracle-calibration-only-<sha>` with the real crop hash.
4. **Verify the render before trusting the hash.** The hash is only as good
   as the picture it came from. Required checks on
   `$BUILD_DIR/terminal-title.rgb`:
   - convert to PNG and look at it — it must read as the word "Terminal";
   - it must not be uniform, and its ink pixels must form ~8 glyph clusters
     inside the 60x18 box;
   - `linux_hosted_wm_live_window_font_identity` must name a real font, not
     `bitmap-default` and not empty;
   - `linux_hosted_wm_live_window_glyph_crop_live_match` must be `true` —
     the X11 window and the framebuffer must agree byte for byte.
5. Only then replace `pending` with the hash, in a comment that records the
   host, the compiler SHA-256, the artefact SHA-256, the font identity and
   the date it was taken.

### Recommended oracle change — pin the font identity too (proposal, not applied)

An exact RGB SHA-256 is defensible **here** because the whole path is
software: the font asset is pinned by SHA-256 (line 16-17), the rasteriser
is in-tree Simple, the crop geometry is fixed, and the gate already proves
the presented X11 pixels equal the computed framebuffer. There is no GPU or
system font-config in the loop, so the usual "hashes are brittle across
drivers" objection does not apply as strongly as it normally would.

The real hole is different: the gate reads `font_identity` out of the
frame-presented log line and only rejects empty or `bitmap-default`. It
does **not** pin which instance was selected. `NotoSansMono[wdth,wght].ttf`
is a *variable* font; a different axis instance is a different rasterisation
and therefore a different — but equally "valid-looking" — hash. Showcase
cell 3 has already been caught selecting a variable instance
(`axes=wght=100`) where a pinned static face was expected.

Proposal: alongside `GLYPH_RGB_SHA256`, pin the exact
`linux_hosted_wm_live_window_font_identity` string captured at calibration
time and fail on mismatch. This **strengthens** the gate; it does not
relax it. Not applied unilaterally.

## Triage 2026-08-15 (static, under Stage-4 resource lock)

Blocker #4 (`JsValue.Symbol` used but not declared) appears RESOLVED at
source level: `Symbol(id: i64)` is declared in
`src/lib/common/js/types/js_types.spl:14`, and every `JsValue.Symbol` use in
the tree (`common/js/builtins/object.spl:290`, `common/js/engine/runtime.spl`,
`common/js/engine/vm_object_store.spl`) imports exactly that enum
(`std.common.js.types.js_types`). The sibling `src/lib/js/types` and
`src/lib/nogc_sync_mut/js/types` JsValue enums still lack Symbol but have no
Symbol-using consumers. Blockers #3 (native-build timeout vs host load) and
#5 (real glyph render to hash) remain environment/capture-bound and are
exactly what the current resource lock forbids — deferred, not shortcut.
Deferred verification: rerun
`sh scripts/check/check-linux-hosted-wm-live-window-evidence.shs` on a quiet
host after Stage-4 completes.
