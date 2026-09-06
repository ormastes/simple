# Slim-UI C terminal references (termbox2, ncursesw)

Work package **A08** of `doc/03_plan/ui/slim_kernel_plugin/plan.md`. Two
reference-only C fixtures that implement the **T1** terminal workload from
§8.1 of
`doc/01_research/ui/slim_kernel_plugin/simple_slim_tui_gui_kernel_plugin_design_parallel_plan_2026-09-05.md`,
so the Simple TUI lanes have an external floor to be measured against.

These are **not** production backends and **not** a proposal to adopt either
library. Promoting a provider is an A00 decision.

## What is compared

The T1 contract, identical on both sides and shared with the Simple side
(`scripts/check/check-ui-slim-startup.shs`, written by a sibling agent):

- 80×24 terminal, entered on the **alternate screen**, cleared
- a bordered panel containing the greeting `Hello from Simple UI!`
- a status line (`status: ready | press q to quit`)
- block waiting for a single key; **`q` quits**
- restore: alternate screen off (`\033[?1049l`), cursor shown (`\033[?25h`),
  echo restored, original termios restored

Exit codes are shared by both fixtures: `0` clean, `2` refused (stdin/stdout is
not a tty — **not a T1 run**), `3` terminal is not exactly 80×24, `4` init
failed, `5` input error/EOF before a key.

## Files

| Path | Role |
|---|---|
| `test/05_perf/ui_slim/ref/termbox2/t1_termbox2.c` | fixture, single-header termbox2 |
| `test/05_perf/ui_slim/ref/ncursesw/t1_ncursesw.c` | fixture, wide-char ncurses |
| `.../<name>/build.shs` | build + write `build/ui_slim/ref/<name>.receipt.sdn` |
| `.../<name>/run_t1.shs` | real-pty T1 run, verdict line, `--selftest`, `--timing N` |
| `test/05_perf/ui_slim/ref/run_t1_lib.shs` | shared harness + sabotage fixtures |
| `test/05_perf/ui_slim/ref/vendor/` | vendored upstream — **external path** |

## Upstream pins

| Library | Source | Pin | License |
|---|---|---|---|
| termbox2 | https://github.com/termbox/termbox2 | `cdf62e9990d8b200768780080fb10a4e2f680051` (2026-09-02), vendored subset, `.git` removed | MIT, `vendor/termbox2/LICENSE` verbatim |
| ncursesw | Homebrew `/opt/homebrew/opt/ncurses` (system install, **not vendored**) | `ncursesw6-config --version` = `6.6.20251230`, wide-char build | MIT-style X/Open (upstream install) |

`test/05_perf/ui_slim/ref/vendor/**` is third-party and must be excluded from
owned-code counts per CLAUDE.md § Owned-Code Scope. Adding that prefix to the
CLAUDE.md external-path list is an A00 integration step; A08 does not own that
file.

## Build lines (measured 2026-09-06, Darwin 25.5.0 arm64)

Compiler: `Apple clang version 17.0.0 (clang-1700.6.4.2)`.

```
cc -O2 -Wall -Wextra -std=c99 -D_DARWIN_C_SOURCE \
   -o build/ui_slim/ref/t1_termbox2 test/05_perf/ui_slim/ref/termbox2/t1_termbox2.c

cc -O2 -Wall -Wextra -std=c99 -D_DARWIN_C_SOURCE -DNCURSES_WIDECHAR \
   -I/opt/homebrew/opt/ncurses/include/ncursesw -I/opt/homebrew/opt/ncurses/include \
   -o build/ui_slim/ref/t1_ncursesw test/05_perf/ui_slim/ref/ncursesw/t1_ncursesw.c \
   /opt/homebrew/opt/ncurses/lib/libncursesw.a
```

Both compile clean under `-Wall -Wextra`. The ncursesw archive is named as an
explicit object, not `-lncursesw`, because the flag resolves to the dylib.
`otool -L` on both binaries lists **only** `/usr/lib/libSystem.B.dylib` — the
static claim is proven, not asserted. macOS has no fully static libc, so
libSystem stays dynamic; that is the platform limit, not a build defect.

Sizes (`build/ui_slim/ref/*.receipt.sdn` carries the full detail):

| Fixture | linked | stripped | stripped + re-signed |
|---|---|---|---|
| `t1_termbox2` | 104,488 B | 102,216 B | 119,776 B |
| `t1_ncursesw` | 255,800 B | 231,240 B | 248,032 B |

`strip` invalidates the arm64 ad-hoc code signature, so the stripped copy is
re-signed with `codesign -s -` to stay runnable; the signature blob is larger
than the symbols removed, which is why the re-signed copy can exceed the
unstripped binary. Both numbers are recorded rather than the flattering one.

## Running

```
sh test/05_perf/ui_slim/ref/termbox2/build.shs
sh test/05_perf/ui_slim/ref/termbox2/run_t1.shs            # verdict line, exit 0/1/2
sh test/05_perf/ui_slim/ref/termbox2/run_t1.shs --selftest # sabotage fixtures only
sh test/05_perf/ui_slim/ref/ncursesw/run_t1.shs --timing 10
```

`run_t1.shs` drives the fixture through a **real pty** with `expect`
(`spawn sh -c "stty rows 24 cols 80; exec /usr/bin/time -l <fixture>"`), waits
for the greeting to actually appear before sending `q` — a here-string would
race the greeting — logs the raw pty transcript, strips CSI/OSC sequences, then
asserts the literal greeting bytes plus `\033[?1049l` and `\033[?25h`. Verdict
is the last stdout line: `PASS — 1 run, greeting seen, terminal restored` /
`FAIL — …` / `ERROR — nothing was checked (…)`, exit 0/1/2.

The `--selftest` is fatal and runs before every scan. Four fixtures:

1. a well-behaved stub must **PASS** (non-vacuity — proves the assertions can pass);
2. a stub that paints the greeting but never leaves the alternate screen must **FAIL**;
3. the fixture with stdout redirected to a file must **refuse** (exit 2, zero bytes written) and is never counted as T1;
4. a program that prints the greeting to a non-tty stdout must **not** be accepted as a refusal — the detector has to discriminate.

Both fixtures check `isatty(0) && isatty(1)` themselves before initializing.
This matters: `tb_init()` falls back to opening `/dev/tty`, and
`newterm(NULL, stdout, stdin)` accepts a file, so without the explicit check a
redirected run would have initialized and looked like a T1 pass.

## Diagnostic numbers (2026-09-06, label `diagnostic`)

10 runs each, host load ~8.9 (this box runs other agents concurrently — treat
as an envelope, not a benchmark). `greeting_us` is spawn → greeting bytes on
the pty; it **includes** the `expect` spawn, `stty` and `/usr/bin/time` exec
chain, so it is an upper bound on the fixture. Total wall time is meaningless
here because the fixture blocks on input.

| Fixture | greeting µs median | max | max RSS median | max |
|---|---|---|---|---|
| `t1_termbox2` | 26,863 | 30,268 | 1,638,400 B | 1,671,168 B |
| `t1_ncursesw` | 27,127 | 37,151 | 2,113,536 B | 2,129,920 B |

**No comparison with Simple is claimed here.** The Simple side is measured by
`scripts/check/check-ui-slim-startup.shs` on the same T1 contract under its own
sampling protocol (design §8.5: 20 warmups, ≥100 interleaved samples on an idle
runner). These 10 runs do not meet that bar and exist only to prove the
fixtures are measurable.

## Limits

- **macOS system ncurses is not usable for this fixture.** The SDK ships only
  `libncurses.5.4.tbd` (`tput -V` reports `ncurses 6.0.20150808`), a non-wide
  build; `NCURSES_WIDECHAR` cannot be honoured against it. The fixture requires
  the Homebrew wide-char build and `build.shs` exits `2`
  (`ERROR — nothing was checked`) when `ncursesw6-config` is absent, rather
  than silently falling back to the narrow system library.
- **Terminfo.** The harness pins `TERM=xterm-256color`. ncurses resolves it
  through the terminfo database recorded in the receipt (`infocmp -D`); a host
  with a different or missing entry will fail at `newterm` with exit 4, not
  produce a degraded pass. termbox2 carries its own built-in capability tables
  and does not read terminfo, which is itself a comparison difference worth
  stating rather than hiding behind the word "hello".
- `-fsyntax`-clean and PTY-verified is not visual verification: bytes accepted
  by a pty are not proof an emulator painted them (design §8.1). A terminal
  emulator integration run is a separate lane.
- Only T1 is implemented. T2 (focus/navigation/resize/Unicode corpus) is not.
- Linux is untested; the build scripts branch `stat` by `uname` but no Linux
  run has been made.
