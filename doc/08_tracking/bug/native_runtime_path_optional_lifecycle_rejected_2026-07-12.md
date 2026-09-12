# Native runtime path rejects archives without optional lifecycle hooks

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

**Status (2026-07-15 -> CLOSED-STALE 2026-09-12):** source implemented; fresh native-all bootstrap
execution remains pending.

The native runtime selector rejected the established Vulkan-capable
`libsimple_runtime.a` because it required optional `__simple_runtime_init`,
`__simple_runtime_shutdown`, `rt_cli_arg_count`, and `rt_cli_arg_at` symbols.
Its existing `test_runtime_path_cli_archive_does_not_require_optional_lifecycle_hooks`
fixture intentionally omits those symbols and requires selection.

The selector now requires only the fixture's ABI contract. Small applications
that need argv use the aggregate `rt_cli_get_args` owner rather than assuming
the optional scalar argv functions. A fresh native-all bootstrap deployment is
still required before the pure-Simple Stage2 compiler can consume this source
fix.

The same daemon rebuild exposed three versioned glibc termios functions being
misclassified as stub candidates. They are now shared system symbols, so libc
resolves them during the final link instead of generated fallback objects.

Strict daemon linking then exposed that the Vulkan runtime archive declared no
`rt_volatile_read/write_u{8,16,32,64}` owners. The runtime now provides those
primitive volatile operations directly; application code continues through the
existing `app.io.volatile_ops` facade.

## Triage 2026-09-12
The 2026-07-15 status already noted execution remains pending; still unexecuted 2 months later. Older than 45 days with no cheap repro re-run; closing per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
