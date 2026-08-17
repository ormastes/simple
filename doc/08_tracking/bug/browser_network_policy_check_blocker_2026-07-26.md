# Browser network policy check blocker

- **Date:** 2026-07-26
- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
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
