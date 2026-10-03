# HIR cache serialization retention

Native fixture: `test/fixtures/hir_cache_retention/main.spl`.
Executable specification: `test/05_perf/compiler/hir_cache_store_retention_spec.spl`.
Native and SSpec status: **UNRUN**. No memory or performance PASS is claimed.

Compile the standalone fixture through a pinned, admitted native producer in an
isolated checkout/cache. Do not use the Rust seed as a general test runner.
Record the producer SHA256, producer source commit, fixture source commit,
runtime archive identity and resulting executable SHA256 independently.
Set `SIMPLE_HIR_STORE_PRODUCER_SHA256`,
`SIMPLE_HIR_STORE_PRODUCER_SOURCE_REVISION` and
`SIMPLE_HIR_STORE_SOURCE_REVISION` from those receipts. Echoed environment
identities alone do not admit a build.

Run `<fixture> <absolute-fresh-root> 4` and separately
`<fixture> <different-absolute-fresh-root> 8`, each in a fresh process under the
existing 7 GB guard. Save stdout as `store-4.env` and `store-8.env`. Set
`SIMPLE_HIR_STORE_REPORT_DIR` for the admitted SSpec runner. Keep elapsed and
peak-RSS guard receipts even when a run fails. Do not retry unchanged failures.

The fixture lowers real function bodies before measurement, without priming the
HIR encoder or nonempty frontend memo. It stores a 256-function module first,
followed by smaller modules of varying size. Every store must increase live
managed bytes by at most 64 KiB and live objects by at most 128, allowing bounded
first-use bookkeeping rather than serialized payload retention. It then reloads
every module after all scopes close and compares complete re-encoded HIR hashes,
including bodies, symbols and spans. Escaped newline/backslash/Unicode warnings
must round trip exactly. A nested-scope refusal must leave the caller's scope
open; a real failed write must close its own scope and permit the next store.
A directory occupying the final cache filename exercises failed atomic rename
after the temporary write. Both failures must obey the same byte/object bounds,
leave the successful-store counter unchanged and allow a subsequent scope.
The store has no file-lock branch; its existing publication uses write/rename.

The 8-module elapsed time must stay below 3 times the 4-module time plus 20 ms.
These budgets remain unmeasured. For a before/after retained-memory
counterfactual, compile the identical fixture against a source differing only
by the store-boundary patch and compare its first-store byte/object/elapsed
metrics. The unpatched fixture is expected to fail the live-growth assertion;
retain its terminal evidence rather than bypassing that assertion. Whole-job
RSS or time from an early-exiting baseline is not comparable with a complete
successful run; representative full-build performance remains a separate gate.

This verifies cache-store scratch only. Cache decode/key calculation, complete
retained parser/HIR ownership, full-inventory target-config and coverage routes
are separate work. Passing it does not establish full builds below 7 GB.
