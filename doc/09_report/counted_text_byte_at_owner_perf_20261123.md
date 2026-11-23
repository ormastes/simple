# Counted text data ownership in byte-at scanning

P3→P3 producer `assembly-v2` (SHA-256`9d25bb34397ef336215956b42b50451e0f876f4b85d09dee1c894a1709783114`) compiled frozen source`0d8f4d2e22e`. Its startup sample retained at `/tmp/simple-rc-build-20261122/p3-self-20261123/startup-sample.txt` contained81/84 samples in `__simple_rt_string_byte_at`→`strlen`:38 from triple-quote scanning,34 line-end scanning, and9 from prefix/import/sibling predicates. This identifies the measured startup window, not every later phase.

## Owner and contract

`rt_string_byte_at` used its stored length for a tagged counted string, but called `strlen` each time a native text ABI handed it the same object's raw data pointer. Scanning N bytes of an N-byte buffer therefore scanned O(N²) bytes. It also returned zero after an embedded NUL, contrary to the same counted object's tagged form.

The runtime already recovers that live counted owner for `rt_string_len`: fixed header offset, alignment/range checks, and the existing sharded hash registry **before reading a candidate header**. Byte-at now reuses that owner. No new pointer cache, string representation, ABI signature or allocation is introduced. The pure-Simple primitive twin checks its existing hashed string registry before reading either tagged or data-borrow headers.

Counted text can contain NUL, and tagged/data-borrow byte access must agree across all its counted bytes. A genuinely foreign C string still ends at its first NUL; changing that buffer changes subsequent results immediately. No foreign-pointer length is cached. Registry retirement is checked after freeing an owner, without dereferencing freed bytes or promising safety for a dangling pointer after allocator reuse.

## Native evidence

The real core-C fixture calls the actual `__simple_rt_string_byte_at` ABI through a volatile function pointer. It verifies tagged and data-borrow UTF-8 bytes around embedded NUL, negative/exact/maximum bounds, empty text, foreign-buffer mutation, interior pointers, and owner retirement. An unreadable guard page proves that a foreign candidate header is not read before registry admission. The original owner fails the embedded-NUL assertion (exit−6); the repaired fixture passes.

Five elapsed-time samples per size, same macOS26.5 ARM64 host, clang-O2 and identical benchmark source:

| Bytes scanned | Baseline p50 / p95 | Candidate p50 / p95 |
|---:|---:|---:|
|65,536|112.649 /122.136ms|0.361 /0.361ms|
|131,072|462.167 /480.220ms|0.722 /0.723ms|
|262,144|1818.456 /1962.733ms|1.446 /1.483ms|

Doubling input cost4.10×/3.93× before,2.00×/2.00× after. At256KiB, peak RSS (`ru_maxrss`, bytes on this host) was2,179,072 before and1,982,464 after; this small absolute difference is not a separate memory-optimization claim. P95 time ratio is0.000756, peak-memory ratio0.909775, and their sum0.910531; neither process approaches the16GiB campaign budget. This is primitive scaling evidence, not an end-to-end bootstrap speed claim.

Artifacts and immutable binary hashes: `/tmp/simple-entry-byte-at-evidence-20261123/summary.sdn`; source baseline, build logs, failed-original assertion, timings and guarded correctness executable are retained in the same directory. `rt_string_byte_at_owner_selfcheck.c` is now a required gate/input in the canonical core-C capsule builder. The pure-Simple native smoke fixture was attempted with the exact qualified assembly-v2 producer, one job, fresh cache, a4GiB canonical cap and900s deadline. It was refused before compilation:6185MiB available was below the8GiB reserve (exit3). The guard receipt confirms quiescence, zero observer errors and enforcement. No reserve/cap was lowered. Execution remains UNRUN pending actual host headroom; source parity alone is not a native PASS. The existing bootstrap-only compiler does not expose `run`, so the optimizer CLI also awaits a qualified full-CLI owner rather than substituting a Rust seed.

## Open follow-up: worker closure materialization

This fix shortens each byte scan; it does not eliminate duplicate closure discovery in worker processes. The campaign also observed `_driver_line_end`→byte-at→strlen in a parse worker while the coordinator's closure had already been resolved. A separate repair should publish a receipt-bound resolved-closure inventory once, let workers consume it read-only, and bind source/SCV content identity, ordered source roots, entry, target/backend, configured variant, producer/runtime identities and relevant compiler options. Negative tests must reject changed/deleted sources, stale SCV epochs, changed configuration and wrong producer/ABI. Workers must retain normal admission and invalidation; merely accepting an old path list is unsafe. Until measured with an exact candidate, this remains open and no elimination-of-duplication claim is made.


## Pure-Simple fixture execution boundary

After host headroom recovered to17,943MiB, a fresh one-job attempt used the same qualified producer,4GiB canonical cap,900s deadline and unchanged8GiB reserve. It parsed and built HIR for3modules, then the compiler crashed with SIGBUS (exit138) during MIR lowering of the fixture before producing an executable. The receipt reports peak411,536KiB, quiescence, zero observer errors and enforced limits. Darwin crash report `simple-2026-11-23-165412.ips` identifies `MirLowering.lower_cast_expr+132`, protection failure`0x442a16ac00`. The fixture has no explicit `as` casts. A separate MIR-owner repair lane is diagnosing that failure; this report makes no pure-Simple runtime PASS claim. Exact command and failure evidence: `/tmp/simple-entry-byte-at-evidence-20261123/run-simple-mirror-2.shs` and `simple-mirror-2/native-build.log(.rss.env)`.
