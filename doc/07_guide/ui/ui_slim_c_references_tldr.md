# Slim-UI C terminal references — TL;DR

Two **reference-only** C fixtures implementing the T1 terminal workload
(80×24, bordered panel, `Hello from Simple UI!`, status line, `q` quits,
terminal restored), so the Simple TUI has an external floor. Not production
backends; adopting a provider is an A00 decision.

- `test/05_perf/ui_slim/ref/termbox2/` — termbox2 pinned at
  `cdf62e9990d8b200768780080fb10a4e2f680051` (MIT), vendored subset under
  `ref/vendor/` (**external path, exclude from owned-code counts**).
- `test/05_perf/ui_slim/ref/ncursesw/` — Homebrew ncursesw `6.6.20251230`
  (wide-char), **not** vendored. macOS system ncurses is 6.0 non-wide and is
  refused, not silently substituted.
- `build.shs` → `build/ui_slim/ref/<name>.receipt.sdn` (compiler, flags, link
  line, linked dylibs, sizes). Both link only `libSystem`; ncursesw is the
  explicit `.a`, since `-lncursesw` picks the dylib.
- `run_t1.shs` → real pty via `expect`, waits for the greeting before sending
  `q`, asserts greeting bytes + `\033[?1049l` + `\033[?25h`. Verdict last line,
  exit 0/1/2. `--selftest` (fatal, 4 fixtures) proves a no-restore fixture
  FAILs and a redirected stdout is refused, never counted as T1.
- Diagnostic only, 10 runs, loaded host: greeting median ≈ 27 ms both; max RSS
  1.64 MB (termbox2) vs 2.11 MB (ncursesw). **No Simple comparison is claimed** —
  that is `scripts/check/check-ui-slim-startup.shs`.

Full guide: `doc/07_guide/ui/ui_slim_c_references.md`.
