# Native llm_caret (Windows) links abort-on-call stubs for rt_tls_* / rt_package_* / rt_dns_lookup

Status: verification-pending (package + dns slice, incl. deadline and tarball); TLS slice open
Date: 2026-11-16

## Census
On the phase-1 seed, the native Windows llm_caret link stubs 31 symbols: 20 `rt_tls_*`, 10 `rt_package_*`, and `rt_dns_lookup`.

This is NOT the #9653 class, where a C file existed but was missing from the core-C archive list in `native_project/tools.rs`:
- `rt_package_*` (except chmod) and `rt_dns_lookup` had no C definition anywhere. They existed only in the Rust runtime (`value/sffi/package.rs`, `value/net_tcp.rs`).
- The only C definitions of `rt_tls_*` are in `runtime_https_openssl_core.c`. That file is OpenSSL and env-gated (`SIMPLE_CORE_C_INCLUDE_HTTPS_OPENSSL=1`), and is deliberately not used.
- `rt_tls_wire_from_bytes` (`runtime_native.c`) and `rt_tls_server_write_bytes` are already backed.

## Fixed (this change)
- `runtime_core_host_services.c` now has C twins of the 10 package leaves. It is already in the archive list. Each leaf delegates to the long-path-aware primitives in `runtime_native.c`:
  - `rt_file_hash_sha256`
  - `rt_file_size`
  - `rt_file_copy`
  - `rt_dir_create_all`
  - `rt_dir_remove_all`
  - `rt_file_exists`
  - `rt_dir_exists`
  - `CreateSymbolicLinkW` or `symlink`
- (superseded, see "DNS deadline + tarball codec" below) the tarball pair first failed closed with -1.
- `runtime_native.c` now defines `rt_dns_lookup` in its winsock section, using `getaddrinfo` and `inet_ntop`. The result is de-duplicated and comma-joined, and is empty on failure.
- No seed rebuild is needed. The runtime C is compiled from the worktree source at native-build time.

## Remaining gaps
- **TLS (20 symbols) is rustls-only.** It has no C lane. The pure-Simple TLS 1.3 client exists at `src/lib/nogc_async_mut_noalloc/tls/client.spl`, but there is no pure-Simple server and no facade with the `tls_sffi.spl` shape.
  - Plan:
    1. Route the caret callers (`infra_mail.spl`, `multimodal_provider.spl`) through a pure-Simple client facade over the noalloc client.
    2. Then do the server side for the STLS/implicit paths (#9110).
  - Until then the stubs abort only if a TLS path is actually called natively.

## DNS deadline + tarball codec (2026-11-16, verification-pending)
- `rt_dns_lookup` now mirrors the Rust twin's bounded lookup: the resolve runs on a worker thread, the caller waits at most 5000 ms, at most 8 lookups are in flight, and a missed deadline returns empty text (the worker is abandoned, not cancelled). Windows waits on the thread handle; POSIX polls an atomic done flag at 1 ms. Hand-off is lockless: an atomic done flag plus an atomic refcount, freed by the last side to drop it. `rt_dns_lookup_timeout_ms(host, ms)` is the new explicit-budget entry; `ms <= 0` answers empty without resolving, like the twin's zero-timeout path.
- `rt_package_create_tarball` / `rt_package_extract_tarball` are real `.tar.gz` in C with no external library. Create writes ustar inside a valid gzip stream of stored deflate blocks (CRC32 trailer), so it is larger than flate2's output but readable by any gunzip/tar. Extract has a full inflate (stored, fixed, dynamic Huffman) plus GNU `L` long names, ustar prefix, and pax headers skipped; absolute, drive, backslash and `..` entry names are refused. Unsupported entry types (symlinks, hardlinks) fail closed with `-1` and a diagnostic.
- Evidence: `scripts/check/native_probes/c_dns_tarball_probe.spl` (native-build with the tip seed, llvm-mingw). RED before the change: `fatal: called unresolved symbol rt_dns_lookup_timeout_ms`.

### Still open
- A real resolver stall is not reproduced in the probe (no slow resolver on the host); the deadline is proven only through the zero-budget path and the resolving path. The wait/abandon branch is code-reviewed, not exercised.
- POSIX branch compiled only by inspection; no Linux clang run on this host.
- Create does not compress; extract reads the whole decompressed archive in memory.
- Extracting archives that carry symlinks (the Rust `tar` unpack would create them) is refused rather than reproduced.
