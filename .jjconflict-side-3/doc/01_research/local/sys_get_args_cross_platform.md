<!-- codex-research -->
# Cross-platform `sys_get_args` local research

The public path is `sys_get_args`/`get_cli_args` -> `rt_get_args` -> the runtime
argument store. Hosted POSIX startup already receives `argc/argv`, but several
execution paths either failed to publish them or read a different store.

- macOS: JIT and SMF dispatch discarded supplied arguments; the Darwin main
  shim also defined a weak no-op `rt_set_args`, which could prevent archive
  extraction of the real provider.
- Linux/BSD: CRT startup correctly calls `spl_init_args`; pure-Simple lacked
  canonical `spl_init_args`, `rt_get_args`, and `sys_get_args` aliases.
- Windows: the MSVC shim used narrow `main(char**)`, losing Unicode arguments,
  and permitted a no-op alternate `rt_set_args` provider.
- SimpleOS: libc used disconnected `simpleos_runtime_*` names, so crt0 could
  publish into a store different from the one read by `sys_get_args`.

The chosen correction is one required startup provider per hosted binary and
canonical aliases backed by one store. Weak SimpleOS C fallbacks remain only so
a strong SimpleCore provider can replace the entire canonical surface.
