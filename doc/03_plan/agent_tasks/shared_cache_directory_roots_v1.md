# Directory ownership delivery

Scope is the existing user-selected Windows/Linux cache verification and
deployment task, including necessary production fixes.

| Responsibility | Owner | Evidence gate |
|---|---|---|
| Native capsule, Simple facade, frontend integration, fixtures/docs | shared_cache_system_tests_astra | Actual C host tests plus generated Simple ABI and frontend checks |
| Independent read-only source review | win_linux_shared_cache_deploy | Resolve concrete review findings before landing |
| Memory reservation and final integration | root | Live process receipts and host capacity |
| Existing native producer lineage | Windows/Linux bootstrap owners | Exact producer/source/runtime receipts |
| Merge and deployment | shared-cache Astra with root coordination | Complete shared-cache acceptance matrix; deployment remains blocked |

Additional sidecars: N/A. No duplicate production host writer. Earlier source
PR 2180 landing is not deployment or proof of cross-host hydration.
