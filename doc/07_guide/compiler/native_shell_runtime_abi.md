# Native legacy shell ABI

`rt_shell_exec(text) -> text` retains the native scalar contract: stdout is
captured, stdin/stderr are inherited, and spawn/allocation failure returns nil.
`rt_shell_exit_code() -> i64` starts at zero per native thread and records the
last scalar call's status. A signal/spawn failure is -1; normal shell exit
codes are preserved on Windows and POSIX.

`rt_shell_exec_tuple(text) -> (text, text, i64)` atomically captures both streams
and exit status without changing the scalar status slot. It uses the real
unbounded process-capture owner, not the fallback that drops stderr. Commands
use `cmd.exe /C` on Windows and `/bin/sh -c` elsewhere. Windows quoted payloads
use the existing `/S` verbatim convention instead of CRT backslash escaping.

Rust supplies strong definitions of all three native ABI names in every feature
configuration, including `native-all-provider`. Its strings, tuples, process
capture and shell status remain in one runtime owner. `runtime_native.c`
provides genuine weak fallbacks for C-only executables: MSVC uses private
`core_c_shell_*` definitions with `/alternatename`; GNU uses weak definitions.
The aggregate selects Rust, while a C-only link selects C. The Rust symbol
retention table keeps the real shell exports in aggregate builds.
Check actual archive exports and successful configured linking, not cfg text
alone. Runtime source edits require fresh authority/fingerprint review and
private output caches; never overwrite a frozen producer or rebind old receipts.

`std.nogc_sync_mut.io.legacy_shell_contract` is an explicit Simple reference:
it composes real tuple capture and TLS scalar-result state transitions. It does
not replace live inherited scalar streams with buffered replay or claim to
implement that host boundary. The annotated SSpec compares actual tuple
capture; its scalar state checks are a model, not native execution evidence.

Focused Windows evidence and limits are in
`doc/08_tracking/bug/native_shell_tuple_status_missing_2026_10_21.md`.
Neither focused native fixtures nor Rust integration tests admit a full
self-hosted test runner, product suite, or cross-host behavior.
