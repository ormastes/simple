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

**OPEN 1 — `nogc_async_mut_noalloc/log/logger.spl` drops hosted errors.**
`runtime_log_hosted.c` stubs every hook to `false`, and its header comment
claims the Simple side then "falls through to its interpreter-safe path
(println / stdio)". It does not: `log_raw` only dispatches to
`target_device_write` / `target_semihost_write` / `target_file_write`. There is
no `println` branch. On a hosted build an error-level message is dropped unless
`targets.spl` happens to map DEVICE to stdout. The comment documents a
fallthrough that was never implemented. Verify `.../log/targets.spl` first.

**OPEN 2 — `common/security/audit_log.spl` never surfaces security events.**
`AuditConfig.default()` sets `log_to_stdout: false`, so a Critical security
event goes only into `tmp/security_audit.log`. A security audit log that no
human reads by default is the worst instance of this class.

**OPEN 3 — `src/lib/*/service/audit_log.spl` has no stderr path at all.**
`audit_append` calls `rt_file_write_text` and nothing else. Its `-> bool` result
is not checked either, so a failed audit write is itself silent.

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
