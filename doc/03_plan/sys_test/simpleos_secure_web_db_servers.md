<!-- codex-design -->
# System test plan: SimpleOS secure web and database servers

## Executable suites

1. `test/03_system/app/server_platform/feature/simpleos_server_lifecycle_spec.spl`: REQ-001/002; NFR-007/008/010.
2. `test/03_system/app/ui_web/feature/secure_web_ssr_interop_spec.spl`: REQ-003/004/006/008/012; NFR-001/002/007/010/011.
3. `test/03_system/database/server/secure_pgwire_server_spec.spl`: REQ-002/005/008/012; NFR-001/002/007/010/011.
4. `test/03_system/network/ssh/secure_ssh_pqc_interop_spec.spl`: REQ-007/008/009/012; NFR-001/002/009/011.
5. `test/03_system/security/hybrid_pqc_provider_spec.spl`: REQ-009/010/011/012; NFR-001/002/006/009.
6. `test/03_system/performance/secure_web_db_server_comparison_spec.spl`: REQ-003/004/005/011/012/013; NFR-003/004/005/006/010.

Generated manuals mirror each path under `doc/06_spec/` after stripping `test/`. Setup uses `@inline`/`@prev`; primary flows remain visible; matrix/hostile/stress mechanics fold. Built-in matchers only.

## Frozen manual steps and helpers

Visible steps include: build/stage release artifacts; boot SimpleOS and launch from filesystem; exchange over bound socket; drain/stop; restart and verify data; render through canonical server path; verify semantic composition and pixel readback; negotiate secure protocol; reject malformed/unauthenticated/downgraded/replayed input; exercise independent oracle; run paired ABBA samples; validate receipts; compare CPU/SIMD/GPU; keep CPU when admission fails.

Shared setup helpers are `setup_release_artifacts`, `setup_simpleos_qemu`, `setup_linux_fixture`, `launch_server_from_filesystem`, `await_listener`, `stop_server_gracefully`, `restart_simpleos`, `send_http_exchange`, `send_pgwire_exchange`, `run_ssh_exchange`, `render_ssr_fixture`, `run_paired_abba`, and `load_benchmark_receipt`.

REQ-004 browser-to-SSR traceability includes a socket-neutral executable seam:
`BrowserHttpTransport` -> canonical `H1Client` request capture ->
`render_ssr_request` -> Engine2D PNG. It must assert method, headers, exact body,
fixture acknowledgement status, independent server status, and PNG dimensions.
The registry acknowledgement is never live socket, TLS, or browser-process
evidence; those acceptance rows retain fail-fast oracles.

Checkers are `check_artifact_receipt`, `check_bounded_lifecycle`, `check_protocol_transcript`, `check_fail_closed`, `check_persistence`, `check_draw_ir_semantics`, `expect_draw_readback`, `check_interop_oracle`, `check_pure_simple_ownership`, `check_resource_counters`, `check_benchmark_contract`, and `check_gpu_admission`.

Any unresolved QEMU/socket, browser/OpenSSL, OpenSSH, pgbench, h2load, physical-GPU, pixel, KAT, or differential oracle must call `fail("UNRESOLVED ORACLE: <name>")`; it may not return synthetic success.

## Evidence

Typed transient evidence uses `protocol`, `exec`, `log`, `binary`, `api`, and `artifact` beneath `build/test-artifacts/<spec-relative-path>/<run-id>/`. Benchmark evidence includes raw ABBA JSONL, summary JSON/CSV, environment/config manifest, hashes, CPU/RSS, errors, and latency distributions. Linux and SimpleOS rows remain separate.
