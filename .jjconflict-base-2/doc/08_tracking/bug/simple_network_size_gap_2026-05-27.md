# Simple Network Size Gap

Date: 2026-05-27

## Summary

The startup/size audit now has working Simple-side TCP, UDP, and plain-HTTP
socket probes through the core-C startup lane, and they are below the C
counter-size target on the audited Linux host.

Current evidence from:

```sh
sh scripts/check-startup-size-performance-audit.shs
```

Current measured rows:

- C TCP connect: `14472` bytes, runs successfully.
- Simple TCP connect: `14328` bytes, runs successfully.
- C UDP send: `14472` bytes, runs successfully.
- Simple UDP send: `14328` bytes, runs successfully.
- C HTTP plain connect: `14472` bytes, runs successfully.
- Simple HTTP plain connect: `14336` bytes, runs successfully.
- C HTTPS OpenSSL connect: `14472` bytes, runs successfully, with
  `8131240` loaded shared-library bytes.
- Simple HTTPS OpenSSL core-C connect: `14336` bytes, runs successfully, with
  `8131240` loaded shared-library bytes.
- Simple HTTPS rustls hosted connect: `431144` bytes, runs successfully, with
  `5904912` loaded shared-library bytes.
- Simple network loaded libraries: `libc.so.6` and `/lib64/ld-linux-x86-64.so.2`.

The Simple rows contain no heavy markers such as `rustls`, `ureq`, `regex`,
`ratatui`, `tauri`, `electron`, or browser/HTML markers.

## Gap

The Simple socket probes are now smaller than the C socket counters: TCP and UDP
are `144` bytes smaller, and plain HTTP is `136` bytes smaller. The hot path is
dependency-clean.

Previous Simple evidence was `30872` bytes through `simple-core`; moving the
audit probes to core-C, removing the broad bootstrap runtime object, splitting
the MCP fast path out of `runtime_native.c`, and compiling core-C objects for
size reduced TCP and UDP by `16544` bytes and plain HTTP by `16536` bytes.

## HTTPS Position

HTTPS is now measured in two explicit lanes:

- The minimized Simple/OpenSSL core-C lane is smaller than the C/OpenSSL
  executable (`14336` versus `14472` bytes) and has the same loaded-library
  footprint.
- The hosted Simple/rustls lane remains much larger as an intentionally separate
  full TLS stack row (`431144` bytes executable).

TCP, UDP, and plain HTTP must stay TLS-free and continue to load only `libc` and
the ELF loader.

## Likely Fix Direction

- Keep the minimal socket primitives in the core-C startup lane and avoid
  importing the existing hosted/interpreter network stack for startup-size
  sensitive binaries.
- Keep a regression gate around these rows because retention of broad runtime
  declarations can quickly reintroduce array/dict/string helpers.
- Keep the OpenSSL HTTPS capsule explicit and separate from TCP/UDP/plain HTTP.
- Continue reducing the hosted rustls lane only if rustls is required for a
  product path; it is no longer the minimized HTTPS startup-size baseline.
