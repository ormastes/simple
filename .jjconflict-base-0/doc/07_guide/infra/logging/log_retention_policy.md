# Log Retention Policy — convert, don't delete

**Rule (user directive 2026-07-18):** when cleaning up debug/probe/instrumentation
logging, do NOT delete the log statements. Convert them to level-gated logs
(debug level, or another fitting level) so they remain reusable for future
debugging. Perf/timing instrumentation is kept as perf-level logging disabled
by config. Deleting is allowed only for overly-specific one-off logs with no
reuse value (e.g. a hardcoded-address dump chasing one dead hypothesis). Most
logs must remain, disabled by default.

## Why

Debugging sessions repeatedly re-add the same probes days or weeks later,
because a stripped probe is knowledge thrown away — the next person (or the
same person) has to rediscover the exact call site, the exact format string,
and the exact values worth printing. A gated probe costs one branch when
disabled and is free to re-enable. Treat instrumentation as an asset, not
scratch work.

## How — hosted/userland code

The repo has a real central facility, not an invented one:

- **`src/lib/log.spl`** — the canonical `std.log` facade (log-lib-drivers
  Phase 5). Levels are `LOG_TRACE=0 .. LOG_OFF=6` (Linux/Zephyr/Rust
  convention). It supports per-subsystem level overrides via an EnvFilter
  string parsed by `log_init_from_config(cfg: text)` (format:
  `"net=debug,vfs=warn,*=info"`), a 4-slot pluggable backend table
  (`log_register_backend` / `log_remove_backend`, kinds: ring/console/
  file/semihost), and a panic-mode flush. It is designed to be usable from
  both userland and driver code (built on a no-GC raw-pointer ABI).
- **`src/lib/nogc_sync_mut/log.spl`** (and its per-tier siblings
  `gc_async_mut/log.spl`, `gc_sync_mut/log.spl`, `nogc_async_mut/log.spl`) —
  the ergonomic entry point most application code should import:
  `use std.log.{log_debug, log_info, log_warn, log_error}`. Gated by the
  `SIMPLE_LOG` environment variable (`trace|debug|info|warn|error|fatal`,
  unset/`off` = silent). When disabled, a log call costs one integer
  comparison. These wrappers dispatch into the `src/lib/log.spl` facade so
  backends registered there still observe the emissions.

Prefer `log_debug` for reusable diagnostic prints and `std.log`'s subsystem
levels when a probe is specific to one subsystem (net, vfs, driver, etc.).

## How — baremetal/kernel code

Two verified patterns exist depending on whether module-level global state is
reliable on the target lane:

- **`src/lib/nogc_async_mut_noalloc/log/`** (`logger.spl`, `targets.spl`,
  `format.spl`, `c_api.spl`) — a no-alloc logging package for
  freestanding/kernel code with no env access: `log_init_serial(level: i32)`
  / `log_init_from_config(config: text)`, `log_set_level(level)`,
  `log_set_targets(targets)`, `log_set_device(kind, base)`, and
  `log_trace/debug/info/warn/error/fatal(msg: text)`. Prefer this where the
  build already links it in.
- **Function-based bool gate** — on lanes where module-global initializers
  are unreliable at runtime (documented freestanding-codegen landmine), use a
  zero-arg function returning a literal bool instead of a module-level
  `val`/`var`, so a flip-to-`true` edit can't silently no-op. Worked example,
  verified in `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`
  (`_probe_debug() -> bool: false`, checked via `if not _probe_debug(): return`
  at the top of the probe function, e.g. `_dbg_vbe_readback`). Use **one
  shared gate per subsystem/file**, not one ad-hoc boolean per log line. See
  `doc/07_guide/os/baremetal/baremetal_simple_codegen_landmines.md` §7
  "Probe caveats" for the established convention this pattern comes from.

## Perf logs

Same rule applies to perf/timing instrumentation: keep it, gated behind a
perf-level log call or a dedicated perf gate/config flag, off by default. Do
not strip timing prints once a perf investigation is done — they are the
fastest way to re-baseline the next regression.

## When deletion is OK

- The log is truly one-off and hypothesis-specific with no reuse value (e.g.
  a hardcoded-address dump chasing a single dead theory).
- **KEEP-ASSERTED rule:** never gate off (or delete) a probe whose output is
  asserted on by a check/gate script (e.g.
  `scripts/check/check-simpleos-*-evidence.shs`). Check for the probe's
  marker string in the relevant script before touching it; if a script
  depends on it, leave it ungated and firing.

## Review checklist

- No log lines are deleted in a cleanup diff unless justified as a genuine
  one-off, non-reusable dump (call it out in the commit/PR description).
- New/converted gates default to **off** (`false`, or `SIMPLE_LOG` unset).
- Gated output is not silently disabled for anything a check/gate script
  asserts on (KEEP-ASSERTED).
- A shared subsystem/file-level gate is reused rather than adding another
  ad-hoc per-line boolean.
