# Showcase matrix — cell "2D x headless (interpreted)" verified GREEN on linux-x86_64

Date: 2026-07-30T15:49:26Z
Host: x86_64-linux

## Verdict

**GREEN.** The 2026-07-26 CLAIMED result reproduces **exactly** on this host,
with today's canonical binary. All five pinned values match:

| Metric | Claimed | Observed | |
|---|---|---|---|
| `graphics_2d_checksum` | 1108808631 | 1108808631 | match |
| `graphics_2d_nonzero` | 76789 | 76789 | match |
| `graphics_2d_semantic_differences` | 4 | 4 | match |
| `graphics_2d_font_cold_rasterizations` | 11 | 11 | match |
| `graphics_2d_font_warm_hits` | 22 | 22 | match |

Font identity resolved and verified:
`sha256=a3041811a78c361b1de50f953c805e0244951c21c5bd412f7232ef0d899af0da;axes=wght=100`
(`NotoSansSC[wght].ttf`), `font_loaded=true`,
`font_backend_attempt_succeeded=true`.

## Provenance

- source commit: `a68cc4abcbb`
- binary: `bin/release/x86_64-unknown-linux-gnu/simple`,
  sha256 `ea4af9a4498297e3c4f31ca74082c20ebb10d7d2cc65218cea022960e15e597d`,
  154,095,344 bytes — the canonical `--profile bootstrap --features llvm` build
  (4/4 provenance markers, `llvm::`=617, `lld::`=0)
- resolution: `SHOWCASE_RESOLUTION=320x240`, software offscreen, interpreted lane

## Reproduce

```bash
cp bin/release/x86_64-unknown-linux-gnu/simple build/tmp/claude_simple
SIMPLE_SHOWCASE_TRACE=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 \
SIMPLE_TIMEOUT_SECONDS=0 SHOWCASE_RESOLUTION=320x240 \
  build/tmp/claude_simple run examples/06_io/ui/graphics_2d_showcase.spl
```

The protected binary name is required: `scripts/resource/kill_simple_monitor.shs`
SIGTERMs any non-protected `simple run` exceeding 95% CPU for 60s, which makes a
slow render look like a hang. `SIMPLE_TIMEOUT_SECONDS=0` is required: `bin/simple
run` applies a hard 10s timeout to any path containing `examples/`.

## MANDATORY precondition — the trap this verification hit first

**The first run of this reproduction FAILED, and the failure was entirely an
artifact of the environment.** It produced `font_loaded=false`,
`font_cold_rasterizations=0`, `font_warm_hits=0`,
`font_backend_attempt_succeeded=false` and a **different checksum**
(1619467208) — while `nonzero` and `semantic_differences` still matched, because
those are dominated by filled geometry rather than glyph coverage.

Cause: the shared working copy has **zero** files under `assets/fonts` — its
`HEAD` predates the font restore (`cdadda01da2`) **and** `core.sparseCheckout=true`,
so the files are absent with a completely clean `git status`. All 57 are present
at origin.

**Two lessons, both load-bearing:**

1. **Verify `assets/fonts` is populated before running any showcase cell.**
   `find assets/fonts -type f | wc -l` must be 57. A partial match on the
   geometry metrics with a checksum mismatch is the signature of a missing font,
   not of a real regression.
2. **A checksum mismatch is not automatically a demotion.** Two of five metrics
   matching is a strong hint the render ran but a resource was missing. Confirm
   the environment before recording a cell as BLOCKED — a false demotion is as
   damaging to the scoreboard as a false PASS.

Run the verification in a worktree checked out at the target commit, not in the
shared sparse working copy.
