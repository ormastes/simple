# Simple HTTPS Size Lane

Date: 2026-05-27
Status: Resolved for the minimized OpenSSL counter lane; hosted rustls remains a
larger separate lane.

## Summary

The startup/size audit now measures TCP, UDP, and plain HTTP through the
core-C startup lane. HTTPS is measured separately through a C/OpenSSL counter,
a minimized Simple/OpenSSL core-C lane, and a Simple/rustls hosted TLS lane. The
current default network rows intentionally stay TLS-free so they can be compared
against the C socket and plain-HTTP counters without inheriting certificate
store or TLS implementation size.

Current nearby evidence from:

```sh
sh scripts/check/check-startup-size-performance-audit.shs
```

Current measured rows:

- C HTTP plain connect: `14472` bytes, runs successfully.
- Simple HTTP plain connect: `14336` bytes, runs successfully.
- Simple HTTP plain loaded libraries: `libc.so.6` and
  `/lib64/ld-linux-x86-64.so.2`.
- Simple HTTP plain markers do not include `rustls`, `openssl`, `boringssl`,
  `mbedtls`, `gnutls`, `ureq`, `curl`, or browser/HTML markers.
- C HTTPS OpenSSL connect: `14472` executable bytes, `8131240` loaded
  shared-library bytes, runs successfully.
- Simple HTTPS OpenSSL core-C connect: `14336` executable bytes, `8131240`
  loaded shared-library bytes, runs successfully.
- Simple HTTPS rustls hosted connect: `431144` executable bytes, `5904912`
  loaded shared-library bytes, runs successfully.

## Existing TLS Code

The repository already has TLS-related surfaces that can inform the separate
HTTPS lane:

- `src/lib/nogc_sync_mut/io/tls_sffi.spl`
- `src/lib/nogc_async_mut_noalloc/tls/`
- runtime hooks named around `rt_tls_*`

These should not be pulled into the TCP, UDP, or plain HTTP startup-size rows by
default.

## Gap

The minimized Simple/OpenSSL executable is `136` bytes smaller than the
C/OpenSSL executable and has equal loaded-library size on this host. The hosted
Simple/rustls executable is still `416672` bytes larger than the C/OpenSSL
executable, so it remains a separate non-baseline row.

## Required Follow-Up

- Keep the C HTTPS counter, Simple/OpenSSL core-C row, and hosted rustls row in
  the audit.
- Keep TCP, UDP, and plain HTTP regression gates TLS-free.
- Continue hosted rustls retention work only if rustls is required for the
  product path.
