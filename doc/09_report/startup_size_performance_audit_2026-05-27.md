# Startup Size Performance Audit

Date: 2026-05-27

## Scope

- Compares minimized C/asm counters with Simple hello and TUI lanes.
- Measures stripped file size, `size` decimal sections, and average process runtime over 20 runs.
- C mmap+argparse is the current baseline for preload-cache startup work.
- Network rows are minimal C socket baselines for future Simple TCP/UDP/HTTP/S size targets.

## Results

| Artifact | Bytes | Dec Section Bytes | Run Status | Avg Runtime ms | Path | Heavy Markers |
|---|---:|---:|---|---:|---|---|
| asm hello syscall | 8568 | 90 | ok | 2.304 | build/startup_size_perf_audit/hello_asm | none |
| C hello write | 14472 | 1998 | ok | 2.464 | build/startup_size_perf_audit/hello_c | none |
| C termios TUI | 14472 | 2426 | ok | 2.369 | build/startup_size_perf_audit/tui_termios_c | none |
| C mmap preload argparse | 14472 | 2800 | ok | 2.453 | build/startup_size_perf_audit/mmap_preload_argparse_c | none |
| C TCP connect | 14472 | 2547 | ok | 2.787 | build/startup_size_perf_audit/tcp_connect_c | none |
| C UDP send | 14472 | 2556 | ok | 2.454 | build/startup_size_perf_audit/udp_send_c | none |
| C HTTP plain connect | 14472 | 2694 | ok | 2.467 | build/startup_size_perf_audit/http_plain_c | none |
| Simple hello core-c-bootstrap | 26864 | 19501 | ok | 2.716 | build/startup_size_perf_audit/hello_simple | none |
| Simple standalone TUI core-c-bootstrap | 26864 | 19696 | ok | 2.553 | build/startup_size_perf_audit/simple_tui_standalone | none |
| Simple full TUI app simple-core | 92312 | 85866 | exit:139 | fail | build/startup_size_perf_audit/simple_tui_app | none |

## Windows And SimpleOS Counterpart Notes

- Linux mmap preload baseline uses `open`, `fstat`, `mmap`, and page-touching every 4096 bytes.
- Windows counterpart should use `CreateFileW`, `GetFileSizeEx`, `CreateFileMappingW`, `MapViewOfFile`, `PrefetchVirtualMemory` when available, and `UnmapViewOfFile`.
- SimpleOS counterpart should use the same preload contract but back it with the OS page/file cache once the kernel VFS/cache path exists; until then, measure explicit read-ahead into the core runtime cache.
- HTTPS is intentionally not linked in this baseline because a real TLS stack changes the target class; Simple should keep TLS behind an explicit runtime feature/capsule.

## Current Direction

- Do not rewrite the TUI from scratch while the standalone Simple TUI remains near the C termios baseline.
- Continue dependency refactoring: keep TUI off GUI/web stacks, keep network/TLS/compression out of default runtime, and make mmap/preload an opt-in core capsule.
