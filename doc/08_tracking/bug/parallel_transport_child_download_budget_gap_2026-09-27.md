# Child transport can transfer beyond a handoff budget

Status: source repair drafted; executable verification pending. Priority: P1.
Owner: Codex root with the parallel transport implementation agent.

Static reproducer: a canonical child handoff may set `max_output_bytes` below
the downloader's global 1 GiB output cap. In
`parallel_transport_child_run_v1.spl`, the child calls
`fetch_build_result_sftp_v1` before `_child_run_inventory_v1` checks the
handoff budget. The fetcher reads the worker manifest, then downloads each
declared output using only the global bound. A result exceeding the handoff
budget therefore consumes transfer and scratch space before the child rejects
it. The failure fetch similarly has no handoff aggregate argument.

Repair: carry a typed transfer limit into the downloader. Reject excessive
file count before SFTP; bound metadata and proof reads; after reading the
manifest, include actual metadata byte counts and declared output sizes in the
aggregate and enforce the per-file limit before each output transfer. Check
actual downloaded sizes as well. Preserve legacy caller behavior through
explicit wrappers. A zero, negative, or inconsistent limit fails closed.

Regression evidence: focused pure budget tests for too many files, too large
per-file output, aggregate excess, exact-bound acceptance, and failure proof
metadata; one adjacent case verifies a smaller valid handoff can pass. A live
transport fixture and source-matched Simple runtime are still required before
production qualification. Keep the child runner unwired until they pass.

The new limited fetch APIs debit actual result, manifest, diagnostic, and
failure-proof bytes separately. The success path checks all manifest-declared
object sizes against the remaining handoff budget before the first object
download, and the child passes its handoff limits to both paths. Legacy callers
retain their prior global bounds and single metadata SFTP batch through wrappers;
only tighter child handoffs use separate capped metadata transfers. The focused
pure budget
spec exists but has not run on a source-matched Simple runtime. The shell's
`ulimit -f` block rounding can transiently allow less than one 1024-byte block
on macOS or 512-byte block on Linux beyond a per-file logical cap; accepted
file bytes are checked exactly. Live transfer, empty failure-manifest, and
legacy-delegation fixtures remain to be exercised.
