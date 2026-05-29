# Startup Size Performance Audit

Date: 2026-05-29

## Scope

- Compares minimized C/asm counters with Simple hello and TUI lanes.
- Measures stripped file size, `size` decimal sections, and average process runtime over 1 runs.
- C mmap+argparse is the current baseline for preload-cache startup work.
- Network rows are minimal C socket baselines for future Simple TCP/UDP/HTTP/S size targets.

## Results

| Artifact | Bytes | Dec Section Bytes | Run Status | Avg Runtime ms | Path | Loaded Libs | Loaded Lib Bytes | Heavy Markers |
|---|---:|---:|---|---:|---|---|---:|---|
| asm hello syscall | 8568 | 90 | ok | 3.250 | build/startup_size_perf_audit/hello_asm | none | 0 | none |
| C hello write | 14472 | 1998 | ok | 2.366 | build/startup_size_perf_audit/hello_c | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| C termios TUI | 14472 | 2426 | ok | 2.625 | build/startup_size_perf_audit/tui_termios_c | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| C mmap preload argparse | 14472 | 2800 | ok | 2.446 | build/startup_size_perf_audit/mmap_preload_argparse_c | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| Simple mmap preload argparse | 14400 | 5669 | ok | 2.487 | build/startup_size_perf_audit/simple_mmap_preload | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| C TCP connect | 14472 | 2547 | ok | 3.804 | build/startup_size_perf_audit/tcp_connect_c | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| Simple TCP connect | 14328 | 2998 | ok | 4.002 | build/startup_size_perf_audit/simple_tcp_connect | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| C UDP send | 14472 | 2556 | ok | 4.563 | build/startup_size_perf_audit/udp_send_c | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| Simple UDP send | 14328 | 3022 | ok | 4.036 | build/startup_size_perf_audit/simple_udp_send | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| C HTTP plain connect | 14472 | 2694 | ok | 3.190 | build/startup_size_perf_audit/http_plain_c | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| Simple HTTP plain connect | 14336 | 3095 | ok | 2.972 | build/startup_size_perf_audit/simple_http_plain | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
| C HTTPS OpenSSL connect | 14472 | 3672 | ok | 7.528 | build/startup_size_perf_audit/https_openssl_c | libssl.so.3,libc.so.6,libcrypto.so.3,/lib64/ld-linux-x86-64.so.2 | 8131240 | none |
| Simple HTTPS OpenSSL core-c connect | 14336 | 3722 | ok | 3.935 | build/startup_size_perf_audit/simple_https_openssl | libssl.so.3,libc.so.6,libcrypto.so.3,/lib64/ld-linux-x86-64.so.2 | 8131240 | none |
| Simple HTTPS rustls hosted connect | 431144 | 420936 | ok | 4.957 | build/startup_size_perf_audit/simple_https_tls | libunwind.so.1,libstdc++.so.6,libm.so.6,libgcc_s.so.1,libc.so.6,/lib64/ld-linux-x86-64.so.2 | 5904912 | none |
| Simple hello core-c-bootstrap | 14336 | 3565 | ok | 2.718 | build/startup_size_perf_audit/hello_simple | libc.so.6,/lib64/ld-linux-x86-64.so.2 | 2125328 | none |
