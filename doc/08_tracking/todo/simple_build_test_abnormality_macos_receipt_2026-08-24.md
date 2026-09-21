# macOS Process-Group Resource Receipt

Status: open; macOS host available, native provider implementation still required.

Owner: runtime/process provider maintainer.

Current source boundary: macOS has process-group/RLIMIT enforcement and legacy bounded execution, but the owned observed provider currently requires Linux pidfds and degrades to `ResourceEvidenceQuality.Unavailable`. Direct-child `ru_maxrss` byte semantics are already handled in the Unix receipt code.

Unblock work:

1. Permit the owned slot lifecycle to use start-identity plus `wait4`/`killpg` when pidfds are unavailable.
2. Retain direct-child CPU/max-RSS and sample descendant processes with documented process-only/sampled-tree quality.
3. Run direct-child, descendant, timeout, signal, and external-cancel fixtures on macOS.
4. Confirm every kill/wait path rejects `pid <= 0` and that unsupported counters remain unavailable.

Resume command on the macOS host: build the source-matched runtime and run `bin/simple test test/03_system/app/perf/feature/simple_build_test_abnormality_detection_spec.spl` with the macOS platform rows enabled.

## 2026-09-21 macOS audit

An aarch64-apple-darwin host is available. Source revision `20245f731db` still
returns `ENOTSUP` from both `owned_process_start` and
`rt_process_owned_poll_v2` under `#ifndef __linux__` in
`src/runtime/runtime_process_owned.c`. `owned_start_identity` returns zero
outside Linux and the start path requires a live pidfd. Merely rerunning the
system spec cannot implement these capabilities.

Keep this item open until a Darwin owner provides a stable start identity,
pins its unreaped child through group signaling and exact wait, and records
truthful direct-child or sampled-tree usage. The existing `ru_maxrss` byte
conversion alone does not admit the provider. The available bootstrap Phase 2
binary has no `test` command; full SSpec execution needs a test-capable admitted
self-hosted binary. Do not record unsupported receipts as platform parity.
