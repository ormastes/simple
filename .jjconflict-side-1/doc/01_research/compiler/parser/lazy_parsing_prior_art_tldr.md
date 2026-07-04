# Lazy Parsing Prior Art — TL;DR

## Bottom Line

Parse signatures eagerly; defer bodies using the indent fence; serialise scope metadata
to avoid O(depth²) re-scan; add a `.smc` cache for warm starts.

## Eager vs. Lazy Parse Flow

```
EAGER (current)                    LAZY (proposed)
                                   
use X                              use X
  |                                  |
  v                                  v
parse ALL bodies              scan signatures only
  |                            (name, params, return)
  v                                  |
symbol table                   symbol table (stubs)
  |                                  |
  v                            first call to fn F
run top-level                        |
                                     v
                              full-parse body of F
                              (replay scope metadata)
                                     |
                                     v
                              execute F
```

## Key Facts per Engine

| Engine | Deferred | Still scanned eagerly | Cache |
|---|---|---|---|
| V8 | AST + bytecode | Scope vars (PreparseData) | Code cache |
| SpiderMonkey | Bytecode | Scope (stencil) | Stencil file |
| JavaScriptCore | Bytecode | Scope | .jsc file |
| rustc | Nothing (query-lazy) | Full parse | Query result cache |
| CPython | Nothing | Full parse | .pyc file |

## Five Actionable Findings

1. **Scope metadata cannot be deferred.** Variable capture (stack vs. heap) must be
   determined at pre-parse time; skip bodies but still track which outer names they
   reference.

2. **Serialise pre-parse results immediately.** Without storing scope metadata alongside
   each deferred body, nested functions are re-scanned on full-parse — O(depth²) cost.
   Store a compact byte array per function (V8's `PreparseData` pattern).

3. **Add a `.smc` module cache (`.pyc` equivalent).** First-load pays lazy-parse cost;
   subsequent loads deserialise cached AST/bytecode directly. Invalidate by content
   hash, not mtime.

4. **Eagerly parse top-level call sites (PIFE rule).** Any `fn` called at module
   top-level should be full-parsed immediately to avoid guaranteed double-parse. Simple's
   indent fence makes these easy to detect.

5. **Expose `--check` / `--eager` mode.** Deferred syntax errors only surface on first
   call; a CI/linting mode should force-parse all bodies at import time to catch errors
   early.
