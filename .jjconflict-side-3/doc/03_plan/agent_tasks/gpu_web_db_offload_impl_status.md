<!-- codex-impl -->
# GPU Web and DB Offload Implementation Status

Status: implementation in progress.

## Implemented Slice

- `src/lib/nogc_sync_mut/web_db_offload/contract.spl`
- `src/lib/nogc_sync_mut/web_db_offload/__init__.spl`
- `test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.spl`
- `test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl`
- `doc/06_spec/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.md`
- `doc/06_spec/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.md`

This slice implements the reliability-first offload decision contract:

- CPU fallback is required before GPU dispatch.
- HTTP/proxy control-plane work remains CPU fallback.
- stale DB generations fall back instead of using GPU results.
- full queues and tiny batches fall back.
- invalid budgets, empty batches, and negative queue depths reject before dispatch.
- GPU evidence is reported only for eligible coarse batches.
- reusable runtime snapshots build web/DB requests through one API.
- reusable execution plans choose GPU library batch targets only after admission.
- reusable queue reservations reserve a single GPU slot for eligible batches.
- reusable batch windows compute average item size and release the queue slot when
  the batch falls back to CPU.
- RAM, SSD, and NoSQL/vector mode gates reject unsafe batches.

## Verified

- `bin/simple check src/lib/nogc_sync_mut/web_db_offload/contract.spl src/lib/nogc_sync_mut/web_db_offload/__init__.spl test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.spl test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl`
- `bin/simple test test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.spl --mode=interpreter`
  - 12 tests passed.
- `bin/simple test test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl --mode=interpreter`
  - 7 scenarios passed.
- `bin/simple spipe-docgen test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.spl --output doc/06_spec`
- `bin/simple spipe-docgen test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.
- `jj git fetch` reports `Nothing changed.`

Attempted broader `bin/simple check src/lib`; it exceeded the 120s tool timeout and left no lingering process.

## Remaining

- Worker-level streaming reverse proxy in `src/lib/nogc_async_mut/http_server/worker.spl`.
- Upstream lookup, header rewrite, timeouts, backpressure, and pooling.
- Web route eligibility integration.
- DB planner/operator integration.
- RAM/SSD/NoSQL storage-mode implementation beyond admission contracts.
- Native/hardware GPU backend beyond deterministic evidence contracts.
- Performance benchmark specs and reports.
