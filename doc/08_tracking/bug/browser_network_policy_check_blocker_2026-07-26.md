# Browser network policy check blocker

- **Date:** 2026-07-26
- **Status:** open (parse blocker no longer reproduces — see 2026-11-25 note; full
  resume sweep still needs a pure-Simple Stage 4 CLI)
- **Scope:** pure-Simple check of browser CORS/HTTP/HTTPS hardening

## Reproduction

```bash
SIMPLE_LIB=src build/bootstrap/stage2_memfix/simple check \
  src/lib/gc_async_mut/gpu/browser_engine/net/cors.spl
```

Three bounded check/fix cycles were run. The first two exposed and corrected
compact boolean expressions and missing `me` markers on instance methods. The
third still failed from the pre-existing line:

```text
line 38: if not is_simple_method(req.method):
expected :, got Ident 'is_simple_method'
```

The parser then emitted cascading errors for the rest of the module. Per the
three-cycle guard, no fourth check was run.

## Resume

On a working pure-Simple Stage 4 CLI, determine whether `if not <call>` is valid
syntax or a parser defect. If invalid, normalize that expression and run the
exact command above once. Then check the changed HTTP/1, HTTP/2, TLS, fetch,
URL, and script-network modules and execute their focused specs. Do not use the
Rust seed as production evidence.

## Triage note 2026-11-25 (p3-bav lane) — parse blocker gone; sweep still needs Stage 4

- `if not <call>:` now parses. Probe on this host (Windows, tracked Rust seed,
  `SIMPLE_LIB=src bin/simple.exe check` on a 5-line fixture containing
  `if not is_simple_method(m):`) produced no parse error, and
  `check src/lib/gc_async_mut/gpu/browser_engine/net/cors.spl` no longer reports
  the line-38 `expected :, got Ident 'is_simple_method'` failure — the exact
  pattern now lives at cors.spl:191 and passes the parser. The seed run emits
  only pre-existing style warnings in unrelated compiler files, then the check
  entry truncates its own stderr (`src/app/cli/check_entry.spl:218`) and exits 1.
- Per this doc's own guard ("Do not use the Rust seed as production evidence"),
  the remaining resume items — checking the HTTP/1, HTTP/2, TLS, fetch, URL and
  script-network modules and running their focused specs on a working
  pure-Simple Stage 4 CLI — were NOT performed here; the tracked binary is the
  Rust seed and no self-hosted binary can be produced in this lane. Left open
  for that sweep only; the original parser-defect blocker itself is resolved.
