# Logging surfaces that suppress error-level output by default (family sweep)

- **Date:** 2026-08-10
- **Status:** PARTIALLY FIXED — `src/lib/nogc_sync_mut/log.spl` fixed here; the
  rest below are OPEN and filed.
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
| `src/lib/nogc_async_mut_noalloc/log/logger.spl` | `log_error` → `rt_simpleos_log_emit`, else `log_raw` | `g_log_level=LOG_INFO`, `g_log_targets=TARGET_DEVICE` | **NO on hosted — OPEN 1** |
| `src/lib/nogc_sync_mut/diag.spl` | `_emit` → stderr, ungated | callers return early unless a `SIMPLE_DIAG` facet is on | YES once called; facets opt-in **by design** |
| `src/lib/common/web/logging.spl` | `Logger.error` → `print` | `min_level` default Info | YES |
| `src/lib/common/security/audit_log.spl` | file append; stderr only if `log_to_stdout` | `log_to_stdout` defaults **false** | **NO — OPEN 2** |
| `src/lib/*/service/audit_log.spl` | `audit_append` → `rt_file_write_text` only | none | **NO — OPEN 3** |
| `src/lib/gc_async_mut/gpu/browser_engine/shared/logging.spl` | `log()` → `print` | `should_log()` discards its level argument | YES — but **inverse defect, OPEN 4** |
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

## OPEN items (not fixed here — each needs its own change)

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
