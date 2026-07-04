# Startup Size Performance Audit

Date: 2026-05-29

## Scope

- Compares minimized C/asm counters with Simple hello and TUI lanes.
- Measures stripped file size, `size` decimal sections, and average process runtime over 20 runs.
- C mmap+argparse is the current baseline for preload-cache startup work.
- Network rows are minimal C socket baselines for future Simple TCP/UDP/HTTP/S size targets.

## Results

| Artifact | Bytes | Dec Section Bytes | Run Status | Avg Runtime ms | Path | Loaded Libs | Loaded Lib Bytes | Heavy Markers |
|---|---:|---:|---|---:|---|---|---:|---|
| asm hello syscall | 8568 | 90 | ok | 4.795 | build/startup_size_perf_audit/hello_asm | none | 0 | none |
| C hello write | 14472 | 1998 | ok | 5.616 | build/startup_size_perf_audit/hello_c | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| C termios TUI | 14472 | 2426 | ok | 4.474 | build/startup_size_perf_audit/tui_termios_c | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| C mmap preload argparse | 14472 | 2800 | ok | 3.543 | build/startup_size_perf_audit/mmap_preload_argparse_c | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| Simple mmap preload argparse | 14400 | 5662 | ok | 4.681 | build/startup_size_perf_audit/simple_mmap_preload | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| C TCP connect | 14472 | 2547 | ok | 4.837 | build/startup_size_perf_audit/tcp_connect_c | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| Simple TCP connect | 14328 | 3004 | ok | 5.556 | build/startup_size_perf_audit/simple_tcp_connect | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| C UDP send | 14472 | 2556 | ok | 5.859 | build/startup_size_perf_audit/udp_send_c | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| Simple UDP send | 14328 | 3028 | ok | 2.832 | build/startup_size_perf_audit/simple_udp_send | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| C HTTP plain connect | 14472 | 2694 | ok | 2.755 | build/startup_size_perf_audit/http_plain_c | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| Simple HTTP plain connect | 14336 | 3101 | ok | 2.975 | build/startup_size_perf_audit/simple_http_plain | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| C HTTPS OpenSSL connect | 14472 | 3672 | ok | 7.397 | build/startup_size_perf_audit/https_openssl_c | libssl.so.3,libc.so.6,libcrypto.so.3,/lib64/ld-linux-x86-64.so.2 | 8131240 | none |
| Simple HTTPS OpenSSL core-c connect | 14304 | 2684 | ok | 2.692 | build/startup_size_perf_audit/simple_https_openssl | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| Simple HTTPS rustls hosted connect | 1933256 | 1925055 | ok | 4.136 | build/startup_size_perf_audit/simple_https_tls | libunwind.so.1,libstdc++.so.6,libm.so.6,libgcc_s.so.1,libc.so.6,/lib64/ld-linux-x86-64.so.2 | 5904912 | openssl:4 |
| Simple hello core-c-bootstrap | 14336 | 3571 | ok | 3.129 | build/startup_size_perf_audit/hello_simple | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| Simple standalone TUI core-c-bootstrap | 14336 | 3753 | ok | 5.295 | build/startup_size_perf_audit/simple_tui_standalone | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| Simple full TUI app core-c-bootstrap | 14368 | 6169 | ok | 6.510 | build/startup_size_perf_audit/simple_tui_app | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |

## Windows And SimpleOS Counterpart Notes

- Linux mmap preload baseline uses `open`, `fstat`, `mmap`, and page-touching every 4096 bytes.
- Windows counterpart source is generated at `build/startup_size_perf_audit/mmap_preload_argparse_win.c`; it uses `CreateFileW`, `GetFileSizeEx`, `CreateFileMappingW`, `MapViewOfFile`, `PrefetchVirtualMemory` when available, and `UnmapViewOfFile`.
- SimpleOS counterpart uses `VfsManager.preload_file_pages(path, page_size)` to warm the filesystem/block-cache path by explicit page-sized read-ahead without coupling VFS to a filesystem's sector map.
- HTTPS is measured as a separate TLS lane because a real TLS stack changes the target class; TCP, UDP, and plain HTTP must remain TLS-free.
- Loaded-library evidence is included to catch regressions where Simple core rows load more shared libraries than the C counters.

## Current Direction

- Do not rewrite the TUI from scratch while the standalone and audited app TUI lanes remain below the C termios baseline.
- Continue dependency refactoring: keep TUI off GUI/web stacks, keep TLS/compression out of default TCP/UDP/plain-HTTP runtime paths, and keep mmap/network probes on the core-C startup lane.
