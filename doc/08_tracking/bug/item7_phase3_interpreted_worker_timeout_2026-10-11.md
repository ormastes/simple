# Item7 Phase3 compiler build: interpreted worker timeout

Status: OPEN. Diagnostic build failed; this is not Phase3 admission evidence.

## Reproduction and immutable inputs

The feature branch targets `release_phase3`. Attempt 1 built
`src/app/cli/bootstrap_main.spl` from feature commit
`33c674a55b518b20679a21acd481d5f410d0b29b` using the private pure-Simple
producer SHA-256
`80030da7da3f15174dc26285389375b19c8f090c29eedb6bded089defaa28071`.
No Rust seed or stub fallback was used.

Packet: `C:/dev/simple-item7-phase3-toolchain-20261011/`.
Request: `request.json`, SHA-256
`4d2e8cdaffcde05983212080fe11a936af5160e3caf9576b879a42fff3c46a8a`.
Clean capture commit: `5d98e5d61ac661a85555516bd4627c2ccb6756e5`.
The app/compiler/lib trees exactly match the feature commit. The runtime
tree `581cd72c145ac010d02e1bd9c0198c82319179ce` differs only by a packet-local,
header-only `runtime_raw_u32.c` compatibility TU required by the producer's
legacy source list. It defines no symbols; the current `runtime_native.c`
remains the sole raw-u32 implementation owner. This composition is diagnostic.

The request uses LLVM, target `x86_64-pc-windows-msvc`, core-C bootstrap runtime,
explicit entry closure, one worker, a 900-second timeout, a 5 GiB enforced
process-tree RSS cap, and a 16 MiB bounded log collector.

## Actual attempt 1 result

`run/result.json` records compiler exit **124**, no executable, and a clean
capture after execution. `run/compile.rss.env` records `status=timeout`,
`quiescent=1`, `rss_cap_enforced=1`, `rss_limit_kib=5242880`, no unexpected
session PIDs, and `peak_rss_kib=4963552` (4.73 GiB). Both observed compiler
processes were gone after the watchdog returned.

The parent spawned one source-run worker:
`run src/app/cli/native_build_worker.spl ... --hir-shard=0/1`.
Before termination that child accumulated 435 seconds of CPU and used about
3.1 GB RSS while the parent waited. The retained terminal log reports
`[hir-shard] completed_workers=1 failed_workers=0 failed_modules=0 unfinished=0`.
This establishes HIR warm-worker completion, not a successful compiler build.

The complete retained stream is 465 bytes, with zero dropped bytes and SHA-256
`7b2c84474c1614602a448019f35db4c6fe6b17acb6a7e01f0fe5f67fdd934da4`.
It does not identify the worker's internal stage during the long CPU interval.

## Cause boundary and bounded continuation

An initial hypothesis attributed the delay to cold SCV inventory over a sparse
checkout's full Git index. The observed HIR child proves the parent had already
passed admission; inventory alone is not an established cause of this timeout.
The general producer route can run compiler worker source through interpretation,
including substantial compiler-module startup. Separating that startup from
active parse/HIR work requires more stage evidence.

Attempt 2 retains the same source, producer, runtime and compatible cache, writes
separate `run2/` receipts, disables the now-completed HIR warm-up with supported
`SIMPLE_HIR_SHARDING=0`, and enables bounded worker/closure/compiler traces.
It retains the same time/memory limits. No internal bootstrap-routing marker is
injected.

## Actual attempt 2 result

`run2/result.json` records compiler exit **88**, `status=rss-cap-exceeded`,
no executable and a clean capture. The final-worker spawn trace was reached;
no HIR warm-up worker was repeated. The resource receipt records
`peak_rss_kib=5244796` against limit `5242880`, `rss_cap_enforced=1`,
`quiescent=1`, and no unexpected session PIDs. This is a resource-aborted
failure, not a timeout or successful compile.

The complete retained stream contains 1666 bytes, with zero dropped bytes and
SHA-256 `f72dcf9b8a6a9bf7c992d73661890b4c7475d0b07e990be4a9176e07c4b48852`.
Request: `request-attempt2.json`, SHA-256
`fd65942591803a8d7700521d69ab730ea6273c8baa1eef25ad58d72aaf1f7473`.
The cache remains retained at its original producer/source/runtime-keyed path.
The final worker's internal phase is still not established by these logs.

The two changed attempts consumed the bounded execution allowance without
producing a candidate. Do not repeat either unchanged or relabel termination
as PASS. The next repair must address worker startup/working-set behavior or
establish an admitted source-matched compiler through the canonical bootstrap
flow; these diagnostics do not authorize bypassing source/runtime admission.

Hello World native sanity and the standalone adaptive loop probe are UNRUN until
a candidate executable exists. Full item7 Simple acceptance tests, source-matched
runner admission, general compiler loop instrumentation and broader typed join
support remain open. The narrow C capture selfcheck PASS does not close them.
