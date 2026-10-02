# HIR cache stores retain encoding scratch

Status: concrete source defect; narrow candidate implemented, native regression
and peak-RSS/performance acceptance **UNRUN**. Not a full bootstrap memory fix.

Windows producer SHA256 `70da44fb1d731afc2dcd27ef095751874c5ea0334937510fec51d11654cce9bb`
was built from source `08e1e3cfc72655614fe5a30d7ace67700faf6f6c`. Its Phase4 LLVM
bootstrap and test-runner stopped under the enforced 7 GB Job cap at HIR 208/1075
and 328/610. The full CLI stopped earlier, parse 2096/2493, so this HIR-store
defect does not explain that parse-stage failure.

Receipts and logs are under
`D:/dev/windows-parser-08e1-validation/phase34-direct-v2/`:
`receipts/phase4-llvm-{bootstrap,test-runner,full-cli}.env.process-tree.env`
and `phase4/llvm/binaries/<name>/compile.{stdout,stderr}.log`.
All three record exit 88 and quiescence. Phase4 tracing was unset.
Corresponding cache roots under `phase34-direct/phase4/llvm/binaries/` contain
195 bootstrap HIR files totaling 106,629,181 bytes and 303 test-runner HIR files
totaling 89,800,816 bytes. These are published bytes, not measured scratch sizes.

`driver_hir_pipeline_lowering.spl` calls `hir_cache_store` after
`lower_retained_surface_module` closes its transient owner. The store calls
`hir_module_encode`, whose local writer allocates escaped lines, chunk arrays,
joined chunks and a final payload, then creates warning/header/publication
strings. Previously none of these allocations had a reclaiming scope.
The no-GC runtime therefore retained them once per cold stored module.

The candidate opens a scope after cache eligibility (which initializes the
private immutable frontend memo), runs the unchanged encoder and atomic writer,
and always ends before returning the scalar result. A nested/unavailable begin
returns false without touching another owner's scope. Store refusal and failed
write/rename take the same cleanup path. No graph is promoted.

Escape review: `HirCodecWriter` is local; generated encoding reads the module
and mutates that writer; escaping is pure text transformation; directory/root
resolution has no mutable memo. Synchronous native write closes its FILE before
returning; rename/delete retain no managed input. Only the scalar store counter
is published. No new raw OS access is introduced; the existing shared transient
facade owns memory boundary calls. Cache bytes, identity and atomic publication
remain unchanged.

The native fixture and performance SSpec cover first encoding, heterogeneous
modules, exact HIR/warning round trips, nested refusal, actual write and rename
failures, subsequent success, failure-path live allocation bounds and elapsed scaling. Before/after
peak-RSS evidence remains required. HIR decode scratch and other parse/HIR
retained owners are not fixed by this change.
