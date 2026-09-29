<!-- codex-design -->
# Stage4 re-export resolver: local research

## Evidence

R6 reached true Stage4 with the verified Stage3 compiler. Its final 512 KiB
of debug trace contained 1,288 `reexport-chase` records but no
`cli_run_file` unresolved-name diagnostic. 1,092 `(facade, wanted)` pairs
were distinct; 98.4% concerned `compiler.10.frontend.core.__init__` (40
imports, 444 exports). This is repeated broad wildcard façade work, rather
than an exact-key recursion cycle.

`ModuleSurfacesByName` is completed through `resolve_export_origins()` and
`finish()` before the HIR lowering loop. Re-export lookup reads that surface
snapshot and its arguments only. However, `HirLowering.begin_module()` resets
the root memo, and a prior attempt to retain it across that method did not
give deterministic results across all lowering-object boundaries. Cache
ownership therefore needs an explicit snapshot owner and generation, rather
than implicit lifetime on a lowering instance.

## Requirements implied by the failure

- Repeated `(facade_name, wanted)` lookups over one finished surface snapshot
  must return the same result, including a miss.
- Memo lifetime must be tied to a named immutable snapshot generation, not a
  module filename or incidental `HirLowering` lifetime.
- Active-path cycle protection remains transient and must never persist a
  branch-local miss as a final answer.
- Tests must cover cyclic miss, cyclic positive, repeated wildcard façade
  negative lookup, and a fresh snapshot invalidating a previous answer.

## Non-goals

- Do not change parser tags, import syntax, or public CLI command APIs.
- Do not use a source-level import workaround as the resolver's long-term
  correctness mechanism.
