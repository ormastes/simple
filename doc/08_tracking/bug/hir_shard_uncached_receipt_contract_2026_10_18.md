# HIR shard codec refusal incorrectly reports CACHE_STORED

Status: source correction and controls authored; runtime verification pending.

## Evidence

Release change `0460db6c7f0` allowed `lower_streaming_hir_shard_receipt_transaction_v1` to finish after a non-I/O codec refusal, but returned the same status 1 as a successful store. Its integer wrapper forwarded that status unchanged. The production streaming shard caller used `not source_failed` as `hir_shard_finish`'s cache flag, so the real terminal writer recorded `CACHE_STORED` despite the refused blob. Recovery accepts both cache states; this finding establishes inaccurate durable-cache evidence, not an observed downstream miscompile.

A second path skipped the store when `parser_record` was empty and then consulted the global last-refusal reason. A stale non-I/O reason could therefore turn missing parser evidence into successful uncached work. Neither path is justified by the intended codec-refusal fallback.

## Correction

The transaction contract distinguishes status 0 (cache hit), 1 (new durable store), 2 (source diagnostic), 3 (codec-refused uncached completion), and negative infrastructure failures. The actual caller rejects unknown statuses, records stored only for 0/1, and counts both 1/3 as lowered work. Missing parser evidence fails before any refusal query. The local refusal flag survives cleanup without rereading global state.

Workers reclaim the HIR graph; the main build lowers the original source again on a cache miss. Archive publication, declaration registration, custody preparation, promotion, reverse-reference publication and error gates remain unchanged. The archive producer independently refuses failed durable storage, and its production controller still requires archive and declaration-registration receipts. UNCACHED does not waive those archive requirements.

## Controls and remaining evidence

`test/01_unit/compiler/cache/driver_hir_shard_transaction_spec.spl` adds the production cache-flag mapping and a real valid-source transaction with absent parser binding. Existing controls retain actual parser-error reclamation, successful storage and cache-hit checks. The companion manual states the pending native ledger/executable control using `test/fixtures/compiler/hir_shard_scope_reclaim/main.spl`.

No compiler/test execution was performed for this patch. No forced codec-refusal integration run or source branch coverage is claimed. The next admitted producer must establish its own Hello result before native diagnostics. A real refusal row is required to cover the UNCACHED path; a normal successful store does not substitute for it.
