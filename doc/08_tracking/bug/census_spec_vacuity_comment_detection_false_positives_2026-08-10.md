# `census-spec-vacuity` comment detection has three fail-open/fail-loud defects (2026-08-10)

Filed, not fixed: `scripts/check/census-spec-vacuity.spl` was in flight in another
session at filing time (foreign staged deletion in the shared index plus an
untracked rewrite, mtime 04:06). Editing it would have collided. Whoever lands
that rewrite should fold these in.

Evidence for all three below was produced by re-running the comment classification
over the 2026-08-09 census rows (`doc/08_tracking/test/comment_cheat_spec_census_2026-08-09.md`)
with corrected rules, and by reading each product file directly.

## D-S1. A leading `*` is a comment only in C-family files

The scanner treats any line whose trimmed form starts with `*` as a block-comment
continuation. That is a C-family rule. In shell, `*)` is a `case` arm — executable
code, and frequently the exact dispatch the gate exists to prove.

Falsely-hollowed rows confirmed as CODE:

| product | line | actual content |
|---|---|---|
| `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` | 802 | `case` arm (`rust-built`, `rust*seed`, `bootstrap*seed`) |
| `scripts/gui/macos-gui-run.shs` | 72 | `*.spl\|*.smf)` case arm |
| `scripts/check/check-widget-showcase-4k-200fps.shs` | 38 | `*) SIMPLE_BIN_SOURCE="repo-bin"` |
| `scripts/check/check-macos-gpu-2d-live-evidence.shs` | 10 | `invalid-backend` case arm |

Restrict `*`-continuation to `.c/.h/.cpp/.cc/.js/.ld/.rs`.

## D-S2. `#` in a C-family file is a preprocessor directive, not a comment

`#include` / `#define` are code. Falsely-hollowed rows confirmed as CODE:

| product | line | actual content |
|---|---|---|
| `src/runtime/runtime_fork.c` | 50, 74 | `#include "runtime_memtrack.h"`, `#define FORK_CAPTURE_LIMIT ...` |
| `src/runtime/runtime_thread.c` | 13 | `#include "runtime_memtrack.h"` |
| `src/runtime/runtime_sdl3.c` | 30, 33 | `#define SDL3_EVENT_KEY_DOWN UINT32_C(0x300)` etc. |
| `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` | 1657 | `#define RT_PCI_MAX_DEVICES 32` |
| `src/runtime/runtime_simd_dispatch.c` | 657, 871, 939 | `__riscv_vector` guards |

In C-family files only `//`, `/*` and `*` continuations are comments.

## D-S3. Nearest-preceding-path pairing mis-attributes the majority of rows

Already flagged as an "ABSENT caveat" in the census, but it is understated: it also
corrupts the COMMENT_ONLY column, which the census presents as load-bearing.

Of 18 rows that survived D-S1/D-S2 correction and were then checked by hand against
the spec's own `val`-bound receiver, **12 were not comment-cheats at all**:

- mispaired file — needle is real code in the file the spec actually reads:
  `engine2d_gpu_offload_contract` (showcase:365), `simpleos_riscv_network_gate`
  (freestanding_runtime.c:3197), `ws_e2e` (auth_params.spl:25),
  `macos_gui_live_window_gate_source`, `bootstrap_main_source`.
- receiver is not source text at all — runtime output or a return value:
  `jupyter_kernel_export_comm` (subprocess reply line), `stage4_memory_gate`
  (subprocess stdout), `x25519mlkem768_absolute` (an `Err` reason),
  `editor_dock_zone` (render return value), `command_dispatch` (a spec-internal
  list literal).
- deliberate documentation pin: `cpu_hotloop_gate` ("documents the recursion blind
  spot instead of pretending coverage"), `tensor_dimensions` (asserts doc/design/
  Lean artifacts, not product source).

Only 6 of 18 were genuine. The fix is the one already sketched as "scan C": bind the
needle to the receiver's `val`, require that receiver to be a `read_*` of a literal
product path, and exclude negative assertions.

## Impact

D-S1 and D-S2 make the census **over-report** hollowness (16 sound gates hollowed in
the prior pass, 9 more confirmed here). D-S3 makes it over-report by a further ~2x.
None of the three can hide a real cheat, so the gate is fail-loud, not fail-open —
but the noise is high enough that the headline count is not usable as a count.
See the honest-bracket note in
`doc/08_tracking/bug/comment_cheat_absent_capabilities_2026-08-10.md`.
