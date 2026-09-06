# Slim-UI startup harness — TL;DR

Full guide: `ui_slim_startup_harness.md` · Script: `scripts/check/check-ui-slim-startup.shs`

```sh
sh scripts/check/check-ui-slim-startup.shs --selftest          # fatal, 5/5, runs first
sh scripts/check/check-ui-slim-startup.shs \
   --binary src/compiler_rust/target/bootstrap/simple --lane H0 --samples 10 --warmup 3
```

- Lanes: **H0** `run h0_hello.spl` (loader floor) · **T0** `run t0_altscreen.spl`
  (terminal enter/restore, no widgets) · **T1** `ui tui t1_greeting.ui.sdn` through a
  real PTY, quit key `q` sent only after the greeting appears.
- Verdict is the LAST stdout line: `PASS — <n> sample(s), <lane>, median … p95 …,
  label=<diagnostic|certified>` (0) / `FAIL — …` (1) / `ERROR — nothing was checked (…)` (2).
- Transcript without the lane marker is **FAIL**, not a dropped sample; 0 samples
  is **ERROR**. `certified` needs ≥100 samples **and** no bootstrap-seed banner —
  everything measurable today is `diagnostic` (no deployed pure-Simple `ui`).
- Clock probed and recorded (`gdate_ns`/`date_ns`/`time_wall`), POSIX sh only.
  Memory is a separate run: `max_rss_bytes` (macOS `-l`) vs `max_rss_kbytes`
  (Linux `-v`) — never compared. Any `cargo|native-build|bootstrap` process,
  peers included, ⇒ ERROR. Raw SDN (binary sha256 + mtime) in
  `build/ui_slim/startup/<lane>_<UTC>.sdn`.
- Measured 2026-09-06 (seed, macOS arm64): H0 median 61.714 ms, T0 median
  64.599 ms, **T1 FAIL** — `error[E1002]: function '_simple_binary' not found`
  (the `ui` entry spawns its backend as a separate process; the seed cannot).
  A second guard-quiet run gave 29/34 ms — shared-box noise is ~2x, so a single
  diagnostic run is a smoke check, not a baseline.
- macOS: use `expect`; the `script(1)` fallback is degraded there (tcgetattr on
  FIFO stdin) and untested on Linux.
