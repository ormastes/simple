# Existing coherent SCV owner: final cycle3 diagnostics

Overall **FAIL/HOLD**. The strict link succeeded, but the independent pipe sanity prerequisite exited40/Job0. Root authorized the five previously unrun regular-process SCV cases in the same cycle3; no process retry, source rebuild, shim or fourth cycle occurred. These results do not admit a compiler, qualify concurrent process ownership, or establish a performance improvement.

The cached d958-produced 131-object archive runs the genuine coherent cce SCV acquisition and inventory owners. The private provider replaces exactly one process TU with coherent cce code: 38 archive members, 37 unchanged; the original allocator is unchanged. The 62,642 pinned source files, original members, producer and tooling pins were unchanged after execution. Generated fixture files are observed outputs and are not part of that immutable-source claim.

| Case | Exit | Native wall s | Native CPU s | Job peak RSS KiB | Acquisition ms | Registry before / after |
|---|---:|---:|---:|---:|---:|---:|
| nested | 0 | 2.239901 | 2.234375 | 197732 | 12 | 1529 / 3369 |
| missing | 0 | 4.808575 | 4.765625 | 424688 | 12 | 1545 / 3229 |
| corrupt | 0 | 4.666186 | 4.562500 | 360988 | 58 | 1584 / 3268 |
| cold | 0 | 4.575906 | 4.484375 | 431456 | 2213 | 1489 / 3847 |
| warm | 0 | 0.377395 | 0.359375 | 285276 | 190 | 70 / 2153 |

Native wall/CPU cover the complete native child (fixture preparation, inventory construction, acquisition and assertions), excluding source-pin and collector scans. Job RSS includes the small measurement wrapper; its scope differs from native-child CPU. Acquisition markers time only the first acquisition. Registry counts are object observations, not live-byte accounting or a reclamation bound. Cold and warm are distinct one-shot processes on the same 16-file, approximately16MiB Unicode fixture; warm skips fixture preparation. They are not equivalent workloads for a speedup ratio, nor a paired original/candidate comparison.

Successful cold/warm and recovered-error paths compare every output file with the exact expected Unicode text. Missing and corrupt cases retain the original error across a second complete acquisition. Nested acquisition rejects an already-active transient epoch, leaves that outer epoch active, permits its owner to pause/end it, and permits a fresh epoch afterward; it never accesses a scoped result after ending the outer epoch.

The pipe diagnostic has a confirmed emitted call-boundary mismatch: the runtime string literal value reaches the C `const char*` command parameter without conversion. Its stdout return similarly lacks conversion to a language string. See PROCESS_ABI_AUDIT.md and retained object disassembly. No provider pipe-lifecycle defect is established. UTF-8 pipe behavior, dead-before-drain, EOF/reuse and concurrency remain unqualified.

Still UNRUN or unproven: drift/destination-write failure, cooperative cancellation, exact allocation-byte reclamation, full CLI/build-runner operation, concurrent request ownership, and original-versus-existing paired native performance. The former local-gap baseline failed input admission; no native original baseline exists. No0.1-second, memory-reduction, speedup or production-readiness claim follows. Source changes remain private.

DIAGNOSTIC_SUMMARY.json records exact receipt, binary, archive, provider and source seals. Original cycle3 REQUEST/RESULT/FINAL_PINS remain unchanged; continuation records preserve the failed prerequisite and the later peer-admission transition.

## Evidence seals

This report publishes diagnostics only. Production source and provider changes are not included.

- Original report SHA-256: 0367E516C5642CEE97CF86B6F5E442B6947472366BD1B2B175F166E106350388
- Diagnostic summary SHA-256: 68CE87F7FC009DFD7AD779F5D29A7784333ACFB5C4FEFCC48BFBAA2EF17570D4
- Local packet: build/native_probe/scv-materialization-scratch-20261013/native-cycle3/. These local evidence assets are not distributed with this report.
- nested terminal receipt SHA-256: a9529f3c69ae35730e9a581d5176c9aafd58a3e7849d4facffd4214d61b68a07
- missing terminal receipt SHA-256: c31cfef283392ccffb9c71879d86319c67a610d8e72d3dc26018f3a990b5c9d5
- corrupt terminal receipt SHA-256: dc3ffad1b34dc96a4618ff3aaeca5e1bf307ac8dc3ef990cc40d9478aeedf590
- cold terminal receipt SHA-256: fde4da5402e53cfd0022148fe29b17a85975047f23d9431f0438d1d7a4d16354
- warm terminal receipt SHA-256: a01848dee866b3038cf894345ddfca24eb42f50409d82703b4cbe667526d34e1
