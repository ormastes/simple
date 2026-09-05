# Logging surfaces that suppress error-level output by default (family sweep)

- **Date:** 2026-08-10
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  fixed 2026-08-10 (see the per-item sections below). OPEN 1 was a
  misdiagnosis and is corrected rather than "fixed". Two adjacent defects were
  found on the way and filed separately, NOT fixed:
  `jit_rt_string_data_returns_nil_breaking_extern_calls_2026-08-10.md` and
  `eprint_in_io_runtime_module_is_rerouted_to_stdout_2026-08-10.md`.
- **Class:** silent non-zero exit. An error is written, and no human ever sees
  it. This is the shape that hid the `simple replay` unbounded self-spawn and
  two sibling fork bombs for days.
- **Predecessors:**
  - `doc/08_tracking/bug/std_log_error_never_reaches_stderr_silent_nonzero_exit_2026-08-10.md`
    (`src/lib/log.spl`, fixed by `c5fee72e5b4`)
  - `doc/08_tracking/bug/simple_replay_self_spawns_unbounded_process_chain_2026-08-10.md`
- **Runnable check:** `scripts/check/check-log-error-visible-by-default.shs`

## Fixed in this change

### `src/lib/nogc_sync_mut/log.spl` — default level was LOG_OFF

`_parse_log_level()` returned `0` (== `LOG_OFF`) whenever `SIMPLE_LOG` was unset
or unrecognised, so `GLOBAL_LOG_LEVEL` was `0` and every one of
`fatal`/`error`/`warn`/`info`/`debug`/`trace`/`verbose` skipped its `_emit(...)`.
`SIMPLE_LOG` decided *whether errors existed at all* rather than how verbose the
sub-error output was.

**Reproduction (before the fix), probe calling `error`/`fatal`/`warn`/`info`/`debug`:**

| `SIMPLE_LOG` | lines containing the ERROR marker |
|---|---|
| unset | **1** — a bare, unlabelled copy of the message |
| `error` | **2** — bare copy + `[ERROR] [scope] msg` |

The single line present with `SIMPLE_LOG` unset comes from the *facade*
(`lib.log.log_dispatch_text`, made unconditional for ERROR/FATAL by
`c5fee72e5b4`), not from this module. It carries **no level and no scope**, so
it is indistinguishable from ordinary program output — an operator cannot tell
an error occurred. This module's own labelled line never appeared.

**Fix:** `_DEFAULT_LOG_LEVEL = 2` (`LOG_ERROR`) is the floor returned when
`SIMPLE_LOG` is unset. `SIMPLE_LOG` now selects verbosity *below* the error
threshold. `SIMPLE_LOG=off` is added as an explicit, deliberate opt-out that
still silences everything.

**After (both lanes, `SIMPLE_LOG` unset):** ERROR marker **2** lines
(bare + `[ERROR] [logvis] ...`), FATAL **2**, INFO **0**.

Side effect that had to be guarded: `_ensure_initialized()` enabled on-disk
logging to `.simple/logs/simple_app.log` on `GLOBAL_LOG_LEVEL > 0`. With the new
floor that test is true for every process in the repo, so it now additionally
requires `SIMPLE_LOG` to be set explicitly. Surfacing errors on stderr must not
silently turn on file logging.

## Family table — does an error-level message reach a human by default?

| module | how error is emitted | gate | default-visible? |
|---|---|---|---|
| `src/lib/log.spl` | `log_dispatch_text` → stderr | ungated for ERROR/FATAL | YES (fixed `c5fee72e5b4`) |
| `src/lib/nogc_sync_mut/log.spl` | `_emit` → stderr | `SIMPLE_LOG`, floored at ERROR | YES (fixed here) |
| `src/lib/nogc_async_mut/log.spl` | `export use` re-export | inherits | YES (inherited) |
| `src/lib/gc_async_mut/log.spl` | `export use` re-export | inherits | YES (inherited) |
| `src/lib/gc_sync_mut/log.spl` | `export use` re-export | inherits | YES (inherited) |
| `src/lib/nogc_async_mut_noalloc/log/logger.spl` | `log_error` → `rt_simpleos_log_emit`, else `log_raw` | `g_log_level=LOG_INFO`, `g_log_targets=TARGET_DEVICE` | YES — was emitted but to **stdout**; ERROR/FATAL now stderr (OPEN 1 fixed, filing was wrong) |
| `src/lib/nogc_sync_mut/diag.spl` | `_emit` → stderr, ungated | callers return early unless a `SIMPLE_DIAG` facet is on | YES once called; facets opt-in **by design** |
| `src/lib/common/web/logging.spl` | `Logger.error` → `print` | `min_level` default Info | YES |
| `src/lib/common/security/audit_log.spl` | file append; stderr only if `log_to_stdout` | ERROR/Critical ungated; `log_to_stdout` for lower | YES (OPEN 2 fixed) |
| `src/lib/*/service/audit_log.spl` | `audit_append` → `rt_file_write_text`, failure → `rt_stderr_write` | none | YES, and the `-> bool` result is now checked and returned (OPEN 3 fixed) |
| `src/lib/gc_async_mut/gpu/browser_engine/shared/logging.spl` | `log()` → `print` | `should_log()` compares rank against the stored `min_level` | YES (OPEN 4 fixed: the level filter now actually filters) |
| `src/lib/nogc_async_mut/http_server/access_log.spl` | `print` | handler | N-A (access log, no error level) |
| `src/lib/nogc_async_mut/mcp/log_store.spl` | — | — | N-A (formatter only) |
| `src/lib/nogc_sync_mut/cli_output/log_writer.spl` | `stderr.write_text` | none | YES |
| `src/lib/nogc_sync_mut/aop_debug_log.spl`, `src/compiler/10.frontend/core/aop_debug_log.spl` | ring buffer drained by MCP | `SIMPLE_AOP_DEBUG`, default off | NO — **by design**, debug facility with no error level |
| `src/compiler/80.driver/driver_log_helpers.spl` | `log_error` → `print "[ERROR] …"` | ungated | YES |
| `src/compiler/80.driver/build_log.spl` | record store, `error_count()` | consumer-drained | N-A |
| `src/compiler/00.common/diagnostics/*.spl` and siblings | `static fn error(...)` constructs a value | — | N-A (value constructors; the driver renders) |
| `src/compiler/80.driver/trace_config.spl`, `50.mir/mir_debug_trace_injection.spl`, `90.tools/perf/trace.spl` | instrumentation | `is_enabled()`, off unless asked | N-A (no error level) |
| `src/runtime/startup/baremetal/runtime_log.c` | `rt_simpleos_log_emit` → UART | `g_log_level=INFO`, targets=DEVICE | YES (serial console) |
| `src/runtime/startup/common/runtime_log_hosted.c` | all hooks stubbed `false` | — | N-A by design (see OPEN 1) |

## OPEN items — ALL NOW FIXED (each took its own change; original filings kept for the record)

**OPEN 1 — FIXED, and the original filing was WRONG.** See the correction under
"OPEN 1 correction" below. Original text kept for the record:

**OPEN 1 (as originally filed) — `nogc_async_mut_noalloc/log/logger.spl` drops hosted errors.**
`runtime_log_hosted.c` stubs every hook to `false`, and its header comment
claims the Simple side then "falls through to its interpreter-safe path
(println / stdio)". It does not: `log_raw` only dispatches to
`target_device_write` / `target_semihost_write` / `target_file_write`. There is
no `println` branch. On a hosted build an error-level message is dropped unless
`targets.spl` happens to map DEVICE to stdout. The comment documents a
fallthrough that was never implemented. Verify `.../log/targets.spl` first.

### OPEN 1 correction (2026-08-10) — errors were never dropped; the SINK was wrong

Reproduction contradicted the filing. A probe calling `log_error`/`log_fatal`/
`log_debug` on a hosted build emitted, in **both** the interpreter and jit lanes:

```
[ERROR] Q21_ERROR_MARK
[FATAL] Q21_FATAL_MARK
```

The `println` fallthrough the `runtime_log_hosted.c` header comment promises
**does exist** — it is just not in `logger.spl`. `log_raw` dispatches to
`targets.spl`'s `target_device_write`, whose *own* extern
(`rt_log_target_device_write_bytes`) also fails on a hosted build and ends at
`print msg`. The C comment is accurate; the filing did not read `targets.spl`,
which is exactly what its own last line said to do first. No C change is needed
and none was made.

**The real defect** is which sink that fallthrough used: ERROR and FATAL went to
**stdout**. Under `prog > data.txt 2> errors.log` the diagnostics landed in
`data.txt` and `errors.log` was empty. A diagnostic mixed into the data stream is
the same silent-failure class as one that is dropped — nothing an operator
watches ever shows it.

**Fix:** `targets.spl` gains `target_stderr_write`, built on the `eprint`
*builtin* — not an extern, so it costs a baremetal link nothing, the same reason
`print` is already safe there. `_log_emit` routes `level >= LOG_ERROR` to it on
the hosted fallthrough only. Baremetal is untouched: `rt_simpleos_log_emit`
succeeds there and returns before the fallthrough is reached. Sub-error levels
keep the device/stdout path.

**Before → after (hosted, both lanes):** stderr `0` → `2` ERROR/FATAL lines;
stdout `3` → `1` (WARN only). DEBUG stayed `0` throughout.

**Runnable check:** `scripts/check/check-noalloc-log-error-reaches-stderr.shs`.
Four-sided: labelled-line positives on stderr; a **sink control** (ERROR/FATAL
must have *left* stdout — without it the check passes on the unfixed code, since
`2>&1` hides the sink); a **negative control** (DEBUG, below the default
`LOG_INFO`, emits zero lines on *both* sinks, catching a fix that deleted the
gate); and a **level-scope control** (WARN still appears, and still on stdout,
catching a fix that redirected everything).
**Oracle proof:** removing the `level >= LOG_ERROR` branch yields
`FAIL -- 8 of 14`, exit 1, in both lanes.

**Side effect checked:** none. `logger.spl` has no in-tree consumer
(`/usr/bin/grep -rn` over `src/`, `scripts/`, `config/` found zero importers), and
no new extern symbol was introduced, so no link surface changed.

**Adjacent defect found, filed separately, NOT fixed here:** in the **jit** lane
`rt_string_data(line)` evaluates to Nil, so every `rt_simpleos_log_emit` call
raises `rt_simpleos_log_emit: argument 2 must be an int, got Nil` on stderr. The
call fails to `false`, which is why the fallthrough runs at all — the hosted path
works *by accident of a broken argument marshal*. The interpreter lane does not
do this. See
`doc/08_tracking/bug/jit_rt_string_data_returns_nil_breaking_extern_calls_2026-08-10.md`.

**OPEN 2 — `common/security/audit_log.spl` never surfaces security events.**
`AuditConfig.default()` sets `log_to_stdout: false`, so a Critical security
event goes only into `tmp/security_audit.log`. A security audit log that no
human reads by default is the worst instance of this class.

### OPEN 2 — FIXED 2026-08-10

**Reproduced.** A probe logging a **Critical** `AuthFailure` under
`AuditConfig.default()` emitted **0** stderr lines in both the interpreter and
jit lanes. The file sink was checked rather than assumed, per the filing: it
**works** — `tmp/security_audit.log` gained one `[CRITICAL] ...` entry per run.
So the events were quiet, not lost. That is still the worst instance of this
class: a security audit log no human reads by default.

**Fix:** `log_security_event` now writes to stderr when
`log_to_stdout` is set **or** the severity is `Error`/`Critical`.
`log_to_stdout` keeps its meaning for levels below `Error`. `enabled: false` and
`min_severity` remain the supported ways to turn auditing down, and both are
still honoured — deliberately, the unconditional path sits *after* those two
gates, not before them. `AuditConfig.default()` itself is unchanged, so no
caller's config shape moves.

**Before → after (default config, both lanes):** stderr `0` → `2`
(`[CRITICAL]`, `[ERROR]`); file sink unchanged at `3`; Info stayed `0`.

**Runnable check:** `scripts/check/check-security-audit-critical-reaches-stderr.shs`.
Positives assert the **labelled** `[CRITICAL]`/`[ERROR]` line, not a count.
Controls: sub-`Error` Info emits zero stderr lines (catches a fix that deleted
the filter instead of flooring it); a `min_severity: Critical` config still
suppresses an `Error` event on **both** sinks (proves the unconditional path did
not bypass the floor); `enabled: false` still suppresses a Critical event; and
the file sink must still receive the event (catches a regression that traded the
file for stderr). **Oracle proof:** restoring the bare `if config.log_to_stdout:`
yields `FAIL -- 4 of 14`, exit 1, stderr 2 → 0 in both lanes.

**Side effect checked:** the sibling fix in this family accidentally enabled
on-disk logging repo-wide by raising a level that `_ensure_initialized()` keyed
off. No equivalent here — this module has no lazy-init hook, and the file sink is
governed independently by `config.log_file`, which this change does not touch. The
check also points its fixture's `log_file` at a temp dir so running it never
writes to the repo's `tmp/security_audit.log`.

**OPEN 3 — `src/lib/*/service/audit_log.spl` has no stderr path at all.**
`audit_append` calls `rt_file_write_text` and nothing else. Its `-> bool` result
is not checked either, so a failed audit write is itself silent.

### OPEN 3 — FIXED 2026-08-10

**Enumerated first:** the glob matches **four** files, not one. Only
`src/lib/nogc_sync_mut/service/audit_log.spl` (59 lines) holds an implementation;
`gc_async_mut` and `nogc_async_mut` are `export use` facades over it, and
`gc_sync_mut` is a `export use ... .*` facade over `gc_async_mut`. One fix covers
all four, but the check exercises all four import paths rather than assuming it,
since a facade can drift out of its re-export list.

**Reproduced.** Appending a `LEASE_GRANTED` record to a path under `/proc`
(unwritable) produced **0** stderr lines and the program continued normally, in
both lanes. The record was simply gone.

**Fix, both halves:** `audit_append` now checks `rt_mkdir_p`'s and
`rt_file_write_text`'s `-> bool` results, reports a failure on stderr as
`[ERROR] [audit_log] ...`, and **returns** `bool`. The six typed wrappers
(`audit_lease_granted`, `audit_command`, `audit_daemon_start`, …) propagate it.
The return type is additive — the only in-tree callers,
`service/daemon_base.spl:71,76`, ignore it and still compile, but can no longer
do so *unknowingly*.

**Before → after:** failed append stderr `0` → `1` labelled line, return value
`(none)` → `false`; successful append unchanged at `0` stderr lines and now
returns `true`.

**Runnable check:** `scripts/check/check-service-audit-write-failure-is-loud.shs`.
Asserts the labelled line *and* the returned `false` — the latter is the half a
stderr-only fix would leave broken, which no amount of output-grepping would
notice. Negative control: a **successful** append emits **zero** stderr lines and
the total is asserted as *exactly* 4 (the 4 failing appends), which is what stops
a "fix" that shouts on every append — this is a hot path on every lease grant.
Environment positive-control: the check exits `2` if `/proc/...` turns out to be
writable, so the failure path can never be silently un-exercised.
**Oracle proof:** dropping both result checks yields `FAIL -- 4 of 16`, exit 1,
in both lanes.

**Side effect caught — a second defect, filed separately.** The first
implementation used the `eprint` builtin, and the check went RED: `eprint` inside
a module that imports `std.io_runtime` (this one does) is **re-routed to STDOUT**
with a literal `[STDERR] ` text prefix, and nothing reaches the real stderr fd.
The same builtin in `targets.spl` (OPEN 1, no `io_runtime` import) reaches stderr
correctly, so it is the import that discriminates. Worked around here by
declaring the `rt_stderr_write` extern directly, as
`common/security/audit_log.spl` already did — which is why OPEN 2 never hit it.
See `doc/08_tracking/bug/eprint_in_io_runtime_module_is_rerouted_to_stdout_2026-08-10.md`.
The check asserts on the real fd, so a regression back to `eprint` here is caught.

**OPEN 4 — inverse defect in `gpu/browser_engine/shared/logging.spl`.**
`should_log()` binds `val _level = msg_level` and then ignores it, so the level
filter does nothing and everything prints. Note this is the failure the negative
control in the runnable check exists to catch: a "fix" that removes the gate
rather than flooring it.

### OPEN 4 — FIXED 2026-08-10

**Reproduced.** A `Logger` built with threshold `Error` printed **all five**
levels (`TRACE`, `DEBUG`, `INFO`, `WARN`, `ERROR`) in both lanes.

**Two defects, not one.** The filing named `should_log` binding
`val _level = msg_level` and returning an unconditional `true`. There was a
second, compounding half: `Logger.new(name, level)` accepted a level and
**discarded** it, because the class had no field to hold it. The filter was inert
at both ends, so fixing only `should_log` would have had nothing to compare
against.

**Fix:** `Logger` gains a `min_level` field that `new` actually stores; a
`_level_rank` helper mirrors the ranking used elsewhere in this family; and
`should_log` becomes `_level_rank(msg_level) >= _level_rank(self.min_level)`.
It changes from `fn` to `me` since it now reads `self`.

**Before → after (threshold Error / Info / Trace, of 5 levels, both lanes):**
`5/5, 5/5, 5/5` → `1/5, 3/5, 5/5`.

**Runnable check:** `scripts/check/check-browser-logger-honours-level.shs`. Here
the **negative** assertion is the one that bites — a positive-only probe passed
on the broken code precisely because the broken code printed everything. Each of
the four sub-threshold levels is asserted individually so a failure names the
level that leaked. Plus an `Info` **boundary** case (exactly TRACE/DEBUG
suppressed, INFO/WARN/ERROR emitted once each), which catches a `>` vs `>=`
off-by-one that a single-threshold test would miss; a labelled-line positive at
the threshold, guarding against over-correcting into suppressing everything; and
a permissive `Trace` end proving the gate is level-driven rather than hardcoded
to a new fixed threshold. **Oracle proof:** restoring the `true` body yields
`FAIL -- 12 of 22`, exit 1, in both lanes.

**Side effect checked:** none. `should_log` has no callers outside this file, and
**nothing in the tree constructs this `Logger`** — the browser-engine subsystems
(`net/dns.spl`, `net/fetch.spl`, `style/animation.spl`, …) only *accept* one as a
parameter. The `Logger(name: ...)` literals in `js/engine/` are a different class
of the same name, unaffected. The constructor signature is unchanged, so no call
site moves. Per the log-retention rule no logging was deleted — the sub-threshold
messages are now level-gated, which is what their callers already asked for.

## Runnable check

`scripts/check/check-log-error-visible-by-default.shs` — verdict line last on
stdout, `PASS`/`FAIL`/`ERROR — nothing was checked` (exit 0/1/2).

It is deliberately two-sided:

- **positive** — with `SIMPLE_LOG` unset, `error()` and `fatal()` must each emit
  at least one line, *and* a labelled `[ERROR] [scope] msg` / `[FATAL] …` line.
  The label assertion is what actually catches this bug; a bare-count assertion
  passes on the broken code, because the facade's unlabelled copy is already
  there.
- **negative control** — with `SIMPLE_LOG` unset, `info()` must emit **zero**
  lines. Without this the check passes trivially on a module whose level gate
  was deleted (exactly OPEN 4's shape).
- **opt-out** — `SIMPLE_LOG=off` must still suppress the labelled line.

Run in both the `interpreter` and `jit` lanes, since a log path that works
interpreted can be eliminated or left unresolved in a compiled lane. Both lanes
agreed at every step here.

**Oracle proof:** reverting `_DEFAULT_LOG_LEVEL` to `0` makes the check FAIL —
4 of 11 assertions, exit 1, ERROR marker count dropping 2 → 1 in both lanes.

## Follow-up (2026-08-10) — `rt_simpleos_log_emit` baremetal side is never compiled by anything in-tree; NOT a board-runnable result

Investigated per the board-runnable rule (`.claude/rules/board-runnable.md`)
after the hosted-lane fixes above landed, to check whether they carry any
SimpleOS/board evidence. They do not, and the gap is narrower and more
specific than "undefined at link time" — it is "never built at all":

- `extern fn rt_simpleos_log_emit(level: i64, msg_ptr: i64, msg_len: i64) -> bool`
  is declared once, at `src/lib/nogc_async_mut_noalloc/log/logger.spl:40`, and
  called at `logger.spl:120`.
- Two C definitions exist, matching arity/types exactly:
  `src/runtime/startup/baremetal/runtime_log.c:133` (the real UART emitter,
  intended for SimpleOS) and `src/runtime/startup/common/runtime_log_hosted.c:82`
  (hosted stub, returns `false`).
- `src/compiler_rust/runtime/build.rs:16` and `:185` compile and
  `rerun-if-changed` **only** `startup/common/runtime_log_hosted.c` into
  `libruntime_sffi_c.a` (confirmed present there via `nm`:
  `0000000000000000 T rt_simpleos_log_emit`). `startup/baremetal/runtime_log.c`
  is referenced **only in a comment** at `build.rs:177` — no compile rule, no
  `rerun-if-changed`, nothing.
  `/usr/bin/grep -rl "startup/baremetal" src scripts doc` (excluding
  `compiler_rust/target`) turns up exactly `simpleos_log.rs`, `memory.rs`,
  `build.rs` (comment only), `src/os/kernel/interrupts/idt.spl`,
  `src/os/runtime/baremetal/runtime_minimal.spl`, and
  `scripts/check/check-jit-nested-extern-arg-marshal.shs` — none of which
  contain a compile/link rule for `runtime_log.c`. No SimpleOS image-build
  script under `scripts/os/` (`simpleos-native-build.shs`,
  `build_simpleos_install_image*.shs`, `build_simpleos_llvm_image.shs`, etc.)
  references `runtime_log.c` either.
- So the earlier "OPEN 1 correction" note above ("Baremetal is untouched:
  `rt_simpleos_log_emit` succeeds there") is true only as a statement about the
  *hosted* fallthrough not needing to change — it does not mean the baremetal
  emitter has ever been exercised. `check-jit-nested-extern-arg-marshal.shs:53-54`
  already flags this precisely: its own probe is "NOT board evidence and does
  not exercise the baremetal UART emitter ... which is a different translation
  unit."

**Net:** this is a **build-wiring gap**, not a missing/mismatched extern
declaration and not something a source-level ABI fix (in the style of the
`rt_dir_walk`/`rt_file_read_text` `(ptr,len)` fixes) can address — the arity
and types already match on both sides. What's missing is a SimpleOS AOT/.smf
build step that compiles `src/runtime/startup/baremetal/runtime_log.c` and
links it into a kernel/board image, plus real-firmware-proxy (OVMF/OpenSBI/
EDK2, never `-kernel`/`isa-debug-exit`) or physical-board evidence that the
resulting emitter reaches UART. Neither exists in-tree today. **No code was
changed for this follow-up** — this entry only records the confirmed gap so
the next session doing SimpleOS logging/board work does not have to
re-derive it. Filed rather than fixed because standing up the SimpleOS
image-build C compile step, sysroot, and a real-firmware QEMU boot check is a
multi-file infra task outside a single narrow-scope change.

## Follow-up 2 (2026-08-10) — baremetal emitter WIRED for aarch64 + riscv64; x86_64 still blocked on `rt_port_outb` ownership

The previous follow-up's premise ("this needs a SimpleOS image-build C compile
step that does not exist") was **wrong on the first half**. That step already
exists and has for a while — it is just not in `build.rs`:

- `build.rs` is **host-only**. It produces `libruntime_sffi_c.a` for the Rust
  seed. Adding `startup/baremetal/runtime_log.c` there would be an ODR
  collision with `startup/common/runtime_log_hosted.c` in the *same* archive and
  would still never reach a board. `build.rs` was correctly left alone (only its
  explanatory comment was corrected).
- The real cross-compile pattern is a `for rt_src in runtime_native
  runtime_simd_utf8 ... runtime_memtrack` loop over `src/runtime/$rt_src.c` with
  freestanding `RT_CFLAGS`, archived into the sysroot's
  `libsimple_runtime_native.a` / `libsimpleos_all.a`. It appears in three
  places: `src/os/port/llvm/sysroot.shs` (x86_64 lane ~line 164, aarch64 lane
  ~line 359), `scripts/os/simpleos-sysroot-aarch64.shs:109`, and
  `scripts/os/simpleos-sysroot-riscv64.shs:225`.
- The two `rt_simpleos_log_emit` definitions are therefore **mutually exclusive
  by archive**, not by preprocessor: the host archive never gets the baremetal
  object, the freestanding sysroot archives never get the hosted one. No
  `-z muldefs` is involved on either lane.

**Wired (aarch64, riscv64, and the aarch64 lane of `sysroot.shs`):**
`startup/baremetal/runtime_log` added to the loop; the loop's `-o` now uses
`$(basename "$rt_src").o` so a subdirectory source lands flat in `$RT_BUILD`.

Evidence (`clang`/`ld.lld`, all with
`-Werror=int-conversion -Werror=incompatible-pointer-types -Wall -Wextra`):

| target | compile | undefined syms in `runtime_log.o` | freestanding link | ODR collisions vs the other 9 RT objects |
|---|---|---|---|---|
| `aarch64-unknown-none-elf` | clean | **0** | `probe_aarch64.elf` OK | 0 (678 RT syms vs 6 log syms) |
| `riscv64-unknown-none-elf` | clean | **0** | `probe_riscv64.elf` OK | 0 |
| `x86_64-unknown-none-elf` | clean | **2** (`rt_port_outb`, `rt_port_inb`) | **FAILS** | n/a |

`llvm-objdump -d --disassemble-symbols=rt_log_target_device_write_bytes
probe_aarch64.elf` shows the real per-byte MMIO loop branching on device kind
(`cmp #0x3` NS16550 / `cmp #0x2` PL011 / `cmp #0x1` COM1) with **no libc call**,
and `llvm-nm -u probe_aarch64.elf` is **0** — so the definition linked in is
`runtime_log.c`, not the hosted stub (which has the same six exported names but
reaches libc, and cannot link `-nostdlib`).

**Still blocked — x86_64 only.** On x86 the COM1 path calls
`rt_port_outb`/`rt_port_inb`. Nothing in the built sysroot defines them
(`nm` over `libsimpleos_c.a`, `libsimple_runtime.a`,
`libsimple_runtime_native.a`: 0 hits). The only definitions in the tree are in
`src/runtime/startup/baremetal/runtime_minimal.c:204`, and that TU **duplicates
11 symbols already owned by `runtime_native.o`** in the same archive:
`rt_invlpg`, `rt_read_cr3`, `rt_write_cr3`, and
`rt_volatile_{read,write}_u{8,16,32,64}`. So `runtime_minimal.c` cannot simply
be appended to the x86_64 loop, and appending `runtime_log.c` *alone* would put
an unresolvable `rt_port_outb` into `libsimple_runtime_native.a` — breaking the
SimpleOS link for every program that reaches the log lib. Note also that
`runtime_native.c`'s versions are **host-semantics fakes** (`rt_read_cr3`
returns a static variable, `rt_invlpg` is a no-op), so it is not the right owner
of real port I/O either, and it is compiled into the *host* archive by
`build.rs` too — adding real `outb` there would fault in userspace.

**Next step for x86_64:** decide which TU owns the port-I/O + MMIO family on the
SimpleOS target (split `rt_port_*` out of `runtime_minimal.c` into its own
freestanding TU, or split the 11 shared primitives out of `runtime_native.c`),
then add both to the x86_64 loop. Deliberately not forced here — a partial
wiring would have shipped a broken link. A `TODO(x86_64 UART log)` comment at
the loop in `src/os/port/llvm/sysroot.shs` points back to this entry.

**Board-evidence scope:** this is **AOT-buildable / link-verified only.** No
physical board and no real-firmware QEMU proxy (OVMF pflash / OpenSBI / EDK2)
was run, so per `.claude/rules/board-runnable.md` this is explicitly **NOT** a
board-runnable claim — nothing here demonstrates bytes reaching a UART. The
hosted lane is unaffected: `build.rs`'s source list is byte-identical apart from
a comment, and `runtime_log_hosted.c` still compiles clean under the same
`-Werror` gate.

## Follow-up 3 (2026-08-10) — x86_64 UNBLOCKED and wired; `rt_port_*` gets its own TU

The ownership question is resolved. Per-symbol analysis of the two candidate
owners:

| symbol(s) | `runtime_minimal.c` | `runtime_native.c` | correct freestanding owner |
|---|---|---|---|
| `rt_port_{inb,outb,inw,outw,inl,outl,io_wait}` | **real** `in`/`out` asm under `#if __x86_64__ \|\| __i386__`, no-op stubs elsewhere | **not defined at all** | `runtime_minimal.c`'s — and there is **no conflict**, this family is unique to it |
| `rt_read_cr3`, `rt_write_cr3`, `rt_invlpg` | **real** `mov %cr3` / `invlpg` asm | **host fakes** (`rt_read_cr3` returns a `static uint64_t`, `rt_invlpg` is `(void)addr;`) | `runtime_minimal.c`'s — but not needed by the log lane |
| `rt_volatile_{read,write}_u{8,16,32,64}` (8) | real volatile deref | **identical** real volatile deref | either; genuinely duplicate, semantically equal |

So the previously-recorded "11 duplicated symbols" splits into 3 host-fakes and
8 semantic duplicates — and **none of them is `rt_port_*`**. That reframes the
blocker: it was never an ODR conflict over port I/O, only a barrier to adding
`runtime_minimal.c` *wholesale*.

**Split chosen:** move the `rt_port_*` family out of `runtime_minimal.c` into a
new freestanding TU `src/runtime/startup/baremetal/runtime_port_io.c`, and add
both it and `startup/baremetal/runtime_log` to the x86_64 loop in
`src/os/port/llvm/sysroot.shs`.

Why this and not the alternatives:
- It is the **exact minimal cut**. `rt_port_*` is the only part of
  `runtime_minimal.c` the sysroot needs and the only part with zero overlap
  against `runtime_native.o`, so nothing else has to move or be decided.
- **Moved, not copied** — one global definition site, so no lane can ever see
  two. A `#ifdef`-guarded `runtime_minimal.c` (option b) would have left two
  archives able to drift apart on a preprocessor condition, and would still
  have dragged the BSS/halt/descriptor-table code into every sysroot link.
- It **cascades nowhere**: an exhaustive grep shows no build system compiles
  `runtime_minimal.c` at all (`build.rs` is host-only and lists neither file;
  the sole compile site is the inline `clang` line in
  `test/02_integration/baremetal_build_spec.spl`, which links only
  `crt0.o + runtime_minimal.o` and references no `rt_port_*`). The three
  host-fake symbols therefore never meet their real counterparts anywhere.
- Side benefit: `src/os/kernel/arch/x86/com1_common.spl`, `arch/reset.spl` and
  `arch/x86_32/cpu.spl` already declare `extern fn rt_port_*`; those references
  had **no definition in any sysroot archive** before this change.

**Verification (x86_64), all five gates:**

1. **Compile** — full `sh src/os/port/llvm/sysroot.shs` run exits **0**; the
   new TUs compile clean under
   `-Werror=int-conversion -Werror=incompatible-pointer-types -Wall -Wextra`
   for `x86_64/aarch64/riscv64-unknown-none-elf` **and** `armv7m-none-eabi`.
2. **Undefined symbols** — `llvm-nm -u runtime_port_io.o` = **0**;
   `runtime_log.o`'s 2 (`rt_port_inb`, `rt_port_outb`) are now satisfied by
   `runtime_port_io.o` **in the same archive**.
   `libsimple_runtime_native.a` = 10 members (was 8).
3. **Freestanding link** — `ld.lld -nostdlib --entry=_start probe.o
   runtime_log.o runtime_port_io.o -o probe_x86_64.elf` succeeds;
   `llvm-nm -u probe_x86_64.elf` = **0**.
4. **ODR** — across all 10 members, 656 exported defs, the new objects add
   **0 collisions**. (Pre-existing, unrelated: 14 duplicate defs among
   `runtime_native.o` / `runtime_memory.o` / `runtime_time.o` — `rt_alloc`,
   `rt_free`, `rt_memcpy`, `rt_memset`, `copy_mem`, `rt_ptr_*`,
   `rt_time_now_*`, `rt_mem_guard_stats`. Not introduced here; worth its own
   entry.)
5. **Disassembly** — `llvm-objdump -d` shows
   `rt_log_target_device_write_bytes` branching `cmpl $0x3/$0x2/$0x1` and
   `callq <rt_port_inb>` / `<rt_port_outb>`, whose bodies are the real
   `outb %al, %dx` / `inb` instructions. **0** libc symbols in the ELF.

**Regression** — `scripts/os/simpleos-sysroot-aarch64.shs` and
`scripts/os/simpleos-sysroot-riscv64.shs` both exit **0**; `runtime_log.o` is
present in each `libsimpleos_all.a` with **0** undefined symbols. Host build
untouched: `build.rs` compiles neither `runtime_minimal.c` nor
`runtime_port_io.c` (its only mentions are comments). The armv7m
`runtime_minimal.o` used by `baremetal_build_spec.spl` still compiles clean and
carries **0** `rt_port_*` references, so removing them broke nothing there.

**Board-evidence scope:** still **AOT-buildable / link-verified only.** No
physical board and no real-firmware QEMU proxy (OVMF pflash) run was performed,
so per `.claude/rules/board-runnable.md` this is explicitly **NOT** a
board-runnable claim — nothing here demonstrates bytes reaching a real COM1.
The remaining step for a board claim is an OVMF-pflash boot with serial capture.
