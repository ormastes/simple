# Bug Report: pixel_verify_browser_glass.spl Hangs in Bootstrap Compiler (Post Allocator-Storm Fix)

**ID**: BUG-PIXEL-VERIFY-BROWSER-GLASS-COMPILE-HANG
**Severity**: High (blocks integration test; 120s timeout)
**Status**: Open
**Date**: 2026-04-28
**Component**: Bootstrap compiler (`src/compiler_rust/target/bootstrap/simple`) loading
`test/integration/rendering/pixel_verify_browser_glass.spl` (and its transitive
imports rooted at `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl`).

## Symptom

After this session's 10 perf commits that fixed the documented HTML allocator-storm
O(n^2) hang per `doc/08_tracking/bug/browser_engine_html_parser_hang.md`,
`test/integration/rendering/pixel_verify_browser_glass.spl` still hits the
120s test-runner timeout — but now for a **different reason**.

The hang is now in the **bootstrap compiler before `fn main()` runs**.
The runtime / allocator path documented in the prior bug is never exercised by
this spec because compilation/loading does not complete.

## Important Correction to Prior Framing

A previous read measured "6.8 MiB RSS" and concluded "small RSS rules out the
allocator." That measurement was taken on the **bash wrapper** `bin/simple`,
not on the compiler. Process layout under the wrapper is:

```
simple(348948) [bash wrapper]    7 MiB RSS  1 thread   sleeping in do_poll  (waiting on child)
  simple(348960) [bootstrap]   122 MiB RSS  5 threads  one pinned at 100% CPU
```

Future investigators: always inspect the descendant `target/bootstrap/simple`
process, not the bash wrapper, for compiler resource usage.

That said, the small **bash-wrapper** RSS does not rule out the allocator on its own —
but the empty stdout (below) does rule out the runtime allocator path being reached.

## Reproduction

```bash
cd /home/ormastes/dev/pub/simple
timeout 30 bin/simple test/integration/rendering/pixel_verify_browser_glass.spl
echo "exit=$?"   # 124 = killed by timeout
```

`fn main()` of the spec opens with `print "=== Browser Engine Glass Theme Pixel
Verification ==="` — but stdout is **empty** after 25 seconds, proving the
process never reaches main().

A sibling spec `test/integration/rendering/pixel_verify_minimal.spl` (38 lines,
single small call) **does** reach `fn main()` (prints "Step 1..Step 10" then
errors with `error: semantic: invalid operation: cannot index value of type i64`
in ~30s), so `bin/simple` does flush prints to a piped file when main() runs.
The empty stdout in the failing spec is therefore signal, not buffering.

## Evidence

### procfs snapshot at t=22s

```
=== descendants ===
direct children: 348960
all descendants:  348960

--- pid 348948 (comm=simple) ---
state:
State:  S (sleeping)
VmSize:    24672 kB
VmRSS:      7016 kB
Threads:        1
wchan: do_poll.constprop.0           <-- bash wrapper waiting on child

--- pid 348960 (comm=simple) ---
state:
State:  S (sleeping)
VmSize:   429472 kB
VmRSS:   121800 kB                   <-- real compiler, 121 MiB
Threads:        5
wchan: futex_wait_queue              <-- main thread parked
threads in /proc/348960/task: 348960 348961 348963 348964 348965
  thread 348961 wchan=0       state=R (running)         <-- CPU burner
  thread 348963 wchan=futex_wait_queue state=S (sleeping)
  thread 348964 wchan=futex_wait_queue state=S (sleeping)
  thread 348965 wchan=futex_wait_queue state=S (sleeping)
```

### per-thread CPU usage at t=22s

```
tid 355977 utime=0    stime=0    state=S
tid 355978 utime=1648 stime=552  state=R    <-- ~22s CPU on one thread = 100% pinned
tid 355980 utime=0    stime=0    state=S
tid 355985 utime=0    stime=0    state=S
tid 355986 utime=0    stime=0    state=S
```

Single thread ~100% CPU, no I/O syscalls in flight (`/proc/<tid>/syscall` empty),
`wchan=0` (currently in user space). Other threads idle. Classic **CPU-bound
infinite loop or super-linear algorithm** in single-threaded compiler logic.

### strace (filtered) shows no app I/O

`strace -f -e trace=poll,select,epoll_wait,read,recvfrom,connect,accept,futex,nanosleep,clock_nanosleep`
captures only the bash wrapper subshells doing `uname`/path-detection (PIDs
33644x). Strace did not follow the post-`exec` bootstrap binary effectively;
combined with the procfs evidence above, this confirms there is no display
socket connect, no network, no file polling — pure CPU.

### gdb attach not available

```
Could not attach to process. ... ptrace: Inappropriate ioctl for device.
/proc/sys/kernel/yama/ptrace_scope = 1
```

`/proc/<pid>/stack` likewise denied without CAP_SYS_ADMIN. Direct backtrace
unavailable in this environment; symptom characterization above is from procfs
state, syscall, wchan, and stat fields only.

### Spec pipeline (no display dependency)

`pixel_verify_browser_glass.spl` is purely computational:

```
22: use std.gc_async_mut.gpu.browser_engine.browser_renderer.{render_html_to_pixel_array}
26: fn main() -> i64:
40:     val pixels1 = render_html_to_pixel_array(html1, 200, 200)
70:     val pixels2 = render_html_to_pixel_array(html2, 200, 200)
88:     val pixels3 = render_html_to_pixel_array(html3, 200, 200)
119:    val pixels4 = render_html_to_pixel_array(html4, 200, 200)
141:    val pixels5 = render_html_to_pixel_array(html5, 200, 200)
```

No SDL, no winit, no Wayland, no X11, no window/surface/sdl/wayland identifiers.
"Display wait" can be ruled out unconditionally.

## Root Cause Class

**Compile-time super-linear scaling per `render_html_to_pixel_array` call site.**
Not an infinite loop — termination is reached, but only after the 120s test
runner timeout fires.

### Empirical bisection (Agent M, 2026-04-28)

Measured wall-clock for `bin/simple <repro>.spl` with N call sites of
`render_html_to_pixel_array(h, 200, 200)` in `fn main()`, no other body code:

| body shape                                 | elapsed | exit |
|--------------------------------------------|--------:|-----:|
| no import, `fn main(): 0`                  |   0.06s |    0 |
| import only, no call                       |   0.99s |    0 |
| 1 call site                                |  24.3s  |    0 |
| 2 call sites                               |  44.5s  |    0 |
| 3 call sites                               |  56.7s  |    0 |
| 5 call sites                               |  96.0s  |    0 |
| 5 call sites via `fn do_render(h)` wrapper | 125.2s  |    0 |
| 1 call site inside `while i < 5` loop      | 109.5s  |    0 |
| empty `while i < 5` loop, no call          |   1.05s |    0 |
| 1 call + full Test-1 diagnostic body       |  46.1s  |    0 |

The full failing spec has 5 call sites **plus** ~200 lines of
interpolated-`print`/index/branch body code, which together push it past
120s — hence the test-runner kill. The single 100%-CPU thread observed in
procfs is super-linear compiler work, not a non-terminating loop.

The helper-wrap experiment confirms cost is **per-call-site at the AST level**
(every call expression of `render_html_to_pixel_array` independently inflates
compile time); collapsing the literal arguments behind a one-line forwarder
function does not help — it actually grows the work because the wrapper itself
is now compiled per call site. A loop with one call site also bloats — likely
because monomorphization / inlining of the entire 869-line BrowserRenderer
pipeline closure is duplicated at each invocation expression in the AST.

This is **not** a recurrence of the documented allocator-storm bug
(`browser_engine_html_parser_hang.md`); the runtime allocator path is never
entered before the 120s kill. The prior fixes for that bug (StringBuilder
conversions, rt_slice identity fast path, char_at substitutions) remain
**unverified by this spec** since `render_html_to_pixel_array` is never
reached at runtime.

## Proposed Fix Shape

Two independent paths, both useful:

### A. .spl-layer mitigation (attempted but insufficient)

Naive split into 2 files (tests 1-3 = 3 calls, tests 4-7 = 4 calls) was
attempted on 2026-04-28 and **did not fit** the 120s test-runner budget:
both halves still timed out at 120s. The full diagnostic body adds
~10-22s per test on top of per-call-site cost (1 call + Test-1 body =
46s vs. 24s for the bare call). To fit the budget the split would need
either (a) >=4 files, each with <=2 call sites and stripped diagnostic
prints, or (b) a single file with diagnostic prints removed entirely.
Both options reduce test signal and are workarounds for the compiler
defect described in section B; not landed.

### B. Compiler perf bug (do NOT touch in this rescue)

The real defect lives in the bootstrap compiler's per-call-site
specialization / inlining of large imported function closures. Suggested
next steps, in order, for a future compiler-track agent:

1. With `ptrace_scope` lowered (or in a dev container), capture a `perf
   record -F 99` flamegraph on `target/bootstrap/simple` while compiling
   the 5-call-site repro at `/tmp/pv_5calls.spl` — the hot leaf will name
   the compiler pass.
2. Cross-check whether `browser_renderer.spl` (or any of its
   `gc_async_mut/gpu/browser_engine/*` transitive imports) added a generic
   explosion or a recursive type alias the bootstrap compiler doesn't
   memoize per-call-site.
3. Likely fix shape: memoize call-site specialization keyed on
   (callee_symbol, monomorphization signature) instead of re-walking the
   whole closure body per call expression.

A "skip-when-no-display" guard is **not** appropriate — there is no
display involvement to guard against.

## References

- Prior bug (different root cause, same spec): `doc/08_tracking/bug/browser_engine_html_parser_hang.md`
- Failing spec: `test/integration/rendering/pixel_verify_browser_glass.spl`
- Working sibling (reaches main): `test/integration/rendering/pixel_verify_minimal.spl`
- Renderer entry point: `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl:454`
  (`pub fn render_html_to_pixel_array(html: text, width: i32, height: i32) -> [u32]`)
- Bootstrap compiler binary: `src/compiler_rust/target/bootstrap/simple`
