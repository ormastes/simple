# Linux Secure Server Comparison — 2026-08-14

STATUS: WARN

## Comparable contract

All release rows must use one pinned CPU for the server, a separate pinned load
CPU, the same payload/dataset, concurrency, warmup, durability policy, and
p50/p95/throughput/max-RSS fields. HTTP compares static-file HTTP/1.1 with
nginx. Embedded CRUD compares PureDatabase with SQLite; client/server CRUD
compares the Pure-Simple database server with PostgreSQL. Embedded and network
rows are never compared as equivalents.

## Fresh host probe (unverified operator observations)

No immutable raw command receipt was retained with command, UTC time, exit
status, artifact/log hashes, and output. Every item in this section is therefore
an unverified operator observation and is not retained or measured evidence.

- Unverified operator observation: host Linux exposed nginx 1.24.0, `wrk`, RTX
  A6000 and TITAN RTX.
- Unverified operator observation: the temporary Stage-2 compiler built 43 KiB
  Simple static-server and 222 KiB
  PureDatabase CRUD executable. This compiler is diagnostic-only.
- Unverified operator observation: the static server announced ready but never
  owned a listening socket; `wrk`
  returned connection refused. The process consumed one CPU at 2,156 KiB RSS.
- Unverified operator observation: CRUD exited before timing with
  `validation_failed=insert_present`, followed by an
  invalid-array-handle ABI diagnostic. Maximum RSS was 2,560 KiB.
- Therefore no fresh nginx, SQLite, PostgreSQL, CPU-parity, or improvement row
  is admitted. Optimizing a path that fails correctness would be invalid.

## Retained historical rows (not fresh equivalence proof)

The existing DB report records PureDatabase microseconds for 100 operations:
insert 2131, lookup 356, update 1160, delete 1061, transaction insert 5572.
Its fixed SQLite reference is 247/393/217/184/279 and PostgreSQL reference is
2431/2858/3623/4294/1666. Only lookup meets both; the server row is unavailable.

## CUDA and optionality

CUDA was not inserted into socket or storage handling: neither workload has a
legitimate bulk-compute stage whose transfer and synchronization cost can be
amortized. GPU availability alone is not acceleration evidence. Any future
optional compute stage must be dynamically loaded only after explicit policy
selection, return a bounded encoded receipt to the CPU owner, prove device,
backend, submit, completion and readback, and leave the CPU-only process free
of CUDA library loads. Canonical server, database and filesystem state remains
parent-owned.

## Blockers

- `self_hosted_cli_test_abi_probe_failed`
- `stage2_static_server_listener_not_installed`
- `stage2_puredatabase_invalid_array_handle`
- `postgresql_and_sqlite_clients_unavailable_on_host`
- `no_legitimate_cuda_server_compute_stage`
- `fresh_linux_receipt_missing`
