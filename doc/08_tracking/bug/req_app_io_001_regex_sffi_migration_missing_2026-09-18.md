# REQ-APP-IO-001 regex safe-SFFI migration never landed (regex_sffi is a stub)

- **Filed:** 2026-09-18
- **Status:** OPEN — feature-level debt; the pinning spec stays red until the
  surface is implemented.

## Evidence

`test/01_unit/app/io/legacy_ffi_facades_spec.spl` asserts that
`src/app/io/regex_ffi.spl` re-exports a canonical safe surface from
`app.io.regex_sffi` with no raw `extern fn` / `rt_` references. Both checks
fail because:

- `src/app/io/regex_sffi.spl` is a 3-line stub — no `regex_new` ..
  `is_valid_ipv4` surface exists at all.
- `src/app/io/regex_ffi.spl` still carries the raw extern declarations.

The compression and FTP legs of the same spec were fixed 2026-09-18 by
rerouting `compress_ffi.spl` / `ftp_ffi.spl` to pure
`export use app.io.{compress,ftp}_sffi.{...}` facades (the canonical modules
already existed as full copies). Regex has no canonical module to reroute TO —
it needs the actual safe-SFFI implementation (regex compile/match/replace +
the IP/email/etc. validators the spec pins), which is real feature work under
REQ-APP-IO-001, not a test fix.

## Spec-pin ned surface (from the spec)

first_api: `regex_new`, last_api: `is_valid_ipv4`; facade must read
`export use app.io.regex_sffi.{` and contain no `extern fn`, `@extern(`,
`rt_`, or wildcard `_sffi.*` imports.
