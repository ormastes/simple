# Driver HIR shard transaction ownership

Status: authored controls; execution and coverage measurement pending. This is a manual, not generated run evidence.

Executable specification: `test/01_unit/compiler/cache/driver_hir_shard_transaction_spec.spl`.

| Control | Required observation |
|---|---|
| Ledger cache mapping | Only transaction status 0 (hit) or 1 (new store) reports stored; diagnostic 2, codec-refused uncached 3 and invalid statuses do not. The production shard caller uses this same mapping. |
| Missing parser binding | A real valid source module with an empty cache key returns infrastructure failure and a parser-binding diagnostic; archive/registration remain absent, context retains no HIR body, flat rows return to their starting count, and the transient scope closes. |
| Parser failure | Actual malformed source retains its diagnostic after reclamation and later scratch allocation. |
| Durable store and hit | Actual valid source first stores with status 1, then hits with status 0; neither transaction retains its full body in the context. |

The mapping assertions do not claim to execute a codec-refusal transaction. After an admitted general SSpec runner is available, execute this specification once with real owner APIs. A compiler-only Phase 2/3 binary is not that runner.

Native integration remains separate: use `test/fixtures/compiler/hir_shard_scope_reclaim/main.spl` with real HIR sharding and inspect the retained terminal ledger. A genuinely observed codec refusal must yield `PASS` + `UNCACHED`, no admitted blob for that refused source, successful main-build cache-miss lowering, and actual executable output `hir-scope-body=37 sibling-return=42 checks=2 failures=0`. A run that stores successfully does not cover refusal. Do not manufacture a successful transaction or receipt to fill this gap. Preserve missing-binding and real store-I/O failures as failures. Archive callers must still reject absent archive/registration and refused archive publication.
