# Stage2 windows-gnu link: 112 undefined rt_* symbols

READY FOR OPUS REVIEW. Severity P1. Status: fix-implemented-verification-pending.

Repro: same native-build command as stage2_byte_len_unresolved_symbol (core-c-bootstrap bundle).
Observed: 'Build failed: 112 runtime symbol(s) referenced by generated code have no definition' e.g. rt_bytes_concat, rt_bytes_slice, rt_db_get/put/*, rt_current_time_ms, rt_linux_group_*, rt_tls13_*. Full list: C:/dev/p3new/stage2new/unresolved_s2n7.txt.
SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1 only skips the pre-check; windows-gnu ld.lld still hard-errors because the trap-stub parity retry in native_project/linker.rs was is_msvc-only.
Workaround WA-s2n8: enable retry for gnu + --error-limit=0 (uncommitted seed diff in stage2-rel). Real fix: back the symbols in core-c-bootstrap (rt_db_* via embedded SQL engine, never libsqlite3) or gate callers out of the entry closure.

## Root cause and fix (2026-11-09, PR work/gnu-link-gc-parity)

The premise "back the 112 symbols in core-c-bootstrap" is wrong for most of
the list. The same closure links on Linux with the same core-C archive because
ELF resolves undefined symbols AFTER `--gc-sections`: every one of the 112 is
referenced only from dead code. Over half (`rt_layout_*`, `rt_current_time_ms`,
`rt_storage_init`, `rt_tls13_hkdf_*`, `rt_linux_group_*`, ...) are extern
declarations in `src/lib/nogc_sync_mut/sffi/host.spl` with no implementation in
ANY runtime lane (baselined unbacked-extern debt); the rest (`rt_db_*`, `rt_hlt`,
`rt_renderdoc_*`) live in TUs the core-C lane deliberately excludes.

Two defects produced the error, both in the Rust seed:

1. `stubs.rs` preflight ("runtime symbol(s) ... NULL GOT slot") assumed the final
   link tolerates undefined symbols. True for ELF/Mach-O
   (`--unresolved-symbols=ignore-all` / `-undefined,dynamic_lookup`), false for
   windows-gnu whose `PlatformLinkConfig::windows_mingw()` has neither flag, so
   ld.lld rejects every live undefined symbol itself. The preflight now defers
   whenever `PlatformLinkConfig::tolerates_unresolved_symbols()` is false
   (exactly the existing `SIMPLE_NO_STUB_FALLBACK=1` deferral).
2. The COFF GC-parity retry in `linker.rs` was `is_msvc`-only. ld.lld
   `-m i386pep` resolves before section GC exactly like lld-link, so the gnu
   lane now gets the same retry (`-Wl,--error-limit=0`, trap stubs for exactly
   the reported names, list written beside the binary).

Minimal reproducer (llvm-mingw clang, `--gc-sections`): a TU with two undefined
`rt_*` calls in a `noinline` dead function fails with 2 `undefined symbol`
errors; adding a gnu-clang-compiled trap-stub object links and runs. Phase
runner: drop `SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1` (WA-s2n7) and the uncommitted
linker.rs/stubs.rs patches (WA-s2n8/s2n9/s2n9b) once the seed is rebuilt.
