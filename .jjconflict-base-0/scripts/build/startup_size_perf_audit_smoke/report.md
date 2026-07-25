# Startup Size Performance Audit

Date: 2026-06-04

## Scope

- Compares minimized C/asm counters with Simple hello and TUI lanes.
- Measures stripped file size, `size` decimal sections, and average process runtime over 1 runs.
- C mmap+argparse is the current baseline for preload-cache startup work.
- Network rows are minimal C socket baselines for future Simple TCP/UDP/HTTP/S size targets.

## Results

| Artifact | Bytes | Dec Section Bytes | Run Status | Avg Runtime ms | Path | Loaded Libs | Loaded Lib Bytes | Heavy Markers |
|---|---:|---:|---|---:|---|---|---:|---|
| asm hello syscall | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/hello_asm | n/a | n/a | n/a |
| C hello write | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/hello_c | n/a | n/a | n/a |
| C termios TUI | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/tui_termios_c | n/a | n/a | n/a |
| C mmap preload argparse | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/mmap_preload_argparse_c | n/a | n/a | n/a |
| Simple mmap preload argparse | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/simple_mmap_preload | n/a | n/a | n/a |
| C TCP connect | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/tcp_connect_c | n/a | n/a | n/a |
| Simple TCP connect | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/simple_tcp_connect | n/a | n/a | n/a |
| C UDP send | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/udp_send_c | n/a | n/a | n/a |
| Simple UDP send | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/simple_udp_send | n/a | n/a | n/a |
| C HTTP plain connect | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/http_plain_c | n/a | n/a | n/a |
| Simple HTTP plain connect | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/simple_http_plain | n/a | n/a | n/a |
| C HTTPS OpenSSL connect | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/https_openssl_c | n/a | n/a | n/a |
| Simple HTTPS OpenSSL core-c connect | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/simple_https_openssl | n/a | n/a | n/a |
| Simple HTTPS rustls hosted connect | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/simple_https_tls | n/a | n/a | n/a |
| Simple hello core-c-bootstrap | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/hello_simple | n/a | n/a | n/a |
| Simple standalone TUI core-c-bootstrap | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/simple_tui_standalone | n/a | n/a | n/a |
| Simple full TUI app core-c-bootstrap | n/a | n/a | exit:127 | fail | build/startup_size_perf_audit_smoke/simple_tui_app | n/a | n/a | n/a |

## Windows And SimpleOS Counterpart Notes

- Linux mmap preload baseline uses `open`, `fstat`, `mmap`, and page-touching every 4096 bytes.
- Windows counterpart source is generated at `build/startup_size_perf_audit_smoke/mmap_preload_argparse_win.c`; it uses `CreateFileW`, `GetFileSizeEx`, `CreateFileMappingW`, `MapViewOfFile`, `PrefetchVirtualMemory` when available, and `UnmapViewOfFile`.
- SimpleOS counterpart uses `VfsManager.preload_file_pages(path, page_size)` to warm the filesystem/block-cache path by explicit page-sized read-ahead without coupling VFS to a filesystem's sector map.
- HTTPS is measured as a separate TLS lane because a real TLS stack changes the target class; TCP, UDP, and plain HTTP must remain TLS-free.
- Loaded-library evidence is included to catch regressions where Simple core rows load more shared libraries than the C counters.

## Current Direction

- Do not rewrite the TUI from scratch while the standalone and audited app TUI lanes remain below the C termios baseline.
- Continue dependency refactoring: keep TUI off GUI/web stacks, keep TLS/compression out of default TCP/UDP/plain-HTTP runtime paths, and keep mmap/network probes on the core-C startup lane.

## Normalized Backend Samples

- SDN artifact: `build/startup_size_perf_audit_smoke/backend_samples.sdn`
- Status: unavailable
