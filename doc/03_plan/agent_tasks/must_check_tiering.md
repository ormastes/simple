# Must-Check Tiering Agent Tasks

- `bootstrap_phase_audit`: read-only Stage 1-4 receipt mapping — complete.
- `push_budget_audit`: read-only fail-closed and timing audit — complete.
- `must_check_tests_docs`: read-only test/manual/wiki routing — complete.
- Merge owner and final reviewer: primary Codex agent.
- Generated-manual reviewer: primary Codex agent.
- `windows_hook_installation`: tooling-team owns native Windows linked-worktree
  execution; final reviewer is the primary Codex agent. Resume with the exact
  commands in `doc/03_plan/sys_test/must_check_tiering.md` and retain both
  installer verdicts plus the installed launcher SHA-256.
- `.agents/skills/`: N/A — no agent-side `sp_dev` skill exists; the shared
  implementation and verification skills do not define the must-check ledger.
- `.claude/commands/`: N/A — SPipe development routing is agent/skill owned in
  this repository; the Gemini command and Codex/Claude SPipe instructions are
  the applicable command surfaces.

## Open bootstrap-row resume matrix

These rows stay TODO until the named checker exists and produces real evidence.
Contract/self-tests never promote live or performance acceptance. Merge owner
and final reviewer for every row is the primary high-capability agent.

| Gate | Owner / prerequisite | Exact resume command and retained evidence |
|---|---|---|
| `stage4-tooling-matrix` | compiler/tooling teams; admitted Stage 3 compiler plus CLI/MCP/LSP journals | Run `sh scripts/bootstrap/bootstrap-from-scratch.sh stage4-tooling-matrix --matrix-id=<frozen-id> --compiler-manifest=<stage3-manifest> --cli-journal=<cli> --mcp-journal=<mcp> --lsp-journal=<lsp> --scope=full`; retain `Stage4ToolingMatrixSummaryV1` as the receipt artifact, create a committed `simple.must-check-gate-receipt/v1`, then use `--record-gate-pass stage4-tooling-matrix`. The recorder independently requires 49 terminal rows, full scope, zero required/optional failures or blockers, and `stage4_compiler_files=0`. |
| `windows-hook-installation` | tooling-team; native Windows with two linked worktrees | Run the PowerShell install/check sequence in the system-test plan; retain both verdicts and launcher SHA-256. |
| `caret-local-llm-launch` | llm-caret-team; Slang generation endpoint and Caret provider | Implement `scripts/check/check-caret-slang-inference-bootstrap.shs`, then run it with an admitted Stage 4 CLI; retain provider identity, bounded request/response, timeout, and stop receipt. `local_torch` is not equivalent. |
| `caret-installed-provider-launches` | llm-caret-team; installed and authenticated Claude, Codex, Gemini, and Kimi CLIs | Implement `scripts/check/check-caret-installed-providers-bootstrap.shs`; launch each through Caret with bounded non-destructive prompts/timeouts and retain executable path/hash/version, Caret request/response, exit, and stop receipts. Mock `/bin/echo` lifecycle coverage is not equivalent. |
| `caret-agent-runtime-primitives` | llm-caret-team; production Caret runtime adapter | Implement a bootstrap checker that exercises real launch, status, cancel, stop, and no-leaked-child behavior. Messaging HTTP/MCP coverage is not equivalent. |
| `caret-production-multi-manager-launch` | llm-caret-team; installed provider wrappers and bounded credentials | Launch multiple installed Caret wrappers concurrently, require sustained parent supervision rather than already-exited echo children, then retain poll, stop, exit, and no-leak receipts. |
| `caret-smux-multi-launch` | llm-caret-team; production `os.apps.smux` PTY adapter | Implement `scripts/check/check-caret-smux-multi-launch.shs`, then run it with an admitted Stage 4 CLI; retain launch/capture/resize/cancel/stop receipts. |
| `web-server-request-port` | server team; production listener rather than a simulated handler | Implement `scripts/check/check-web-server-request-port.shs`; bind a configurable loopback port, retain readiness, real request bytes, response bytes/status, listener ownership, bounded shutdown, and no-leak evidence. |
| `web-server-gpu-nginx` | server-performance-team; device-origin GPU offload and a passing request-port receipt | Establish the CPU/nginx baseline with `sh test/perf/bench/http_server/run_bench.shs`; implement `scripts/check/check-web-server-gpu-nginx.shs`, then retain byte-identical CPU/GPU responses, real device-hit counters, and CPU/GPU/nginx throughput and latency on the same request corpus. The baseline or admission decision alone does not pass. |
| `db-server-request-port` | database team; production wire listener rather than direct function calls | Implement `scripts/check/check-db-server-request-port.shs`; bind a configurable loopback port, retain readiness, real query bytes, result bytes/status, listener ownership, bounded shutdown, and no-leak evidence. |
| `db-server-gpu-sql` | server-performance-team; real GPU database path plus passing request-port and PostgreSQL/MySQL fixtures | Establish the Simple baseline with `bin/simple run test/05_perf/db/db_bench_driver.spl`; implement `scripts/check/check-db-server-gpu-sql.shs`, then retain identical CPU/GPU results, real device-hit counters, and Simple/PostgreSQL/MySQL throughput and latency on semantically equivalent data and queries. |
| `simpleos-sbc-qemu-ls` | simpleos-platform-team; written-media receipt and connected UP2 | Run `sh scripts/check/check-simpleos-up-squared-apollo-lake.shs --ovmf`, then `UP2_MEDIA_RECEIPT=<receipt> sh scripts/check/check-simpleos-up-squared-apollo-lake.shs --live`; retain image hash and paired filesystem transcripts. |
| `simpleos-clang-hello` | simpleos-platform-team; admitted compiler | Run `SIMPLE_BUILD_COMPILER=<admitted-stage3> sh scripts/os/build_clang_disk.shs`; retain compiler/source/executable hashes, guest stdout, and exit status. |
| `simpleos-simple-toolchain` | simpleos-platform-team; admitted SimpleOS images | Run `sh scripts/check/check-simpleos-fs-toolchain-qemu-matrix.shs`; retain per-architecture native tool identity and filesystem hello compile/run receipts. |
| `simpleos-server-executables` | SimpleOS + server teams; signed per-architecture receipts and trust key | Run `sh scripts/check/check-simpleos-filesystem-servers-qemu.shs` with its documented receipt/signature environment; retain bounded launch/readiness/request/stop evidence. |
| `riscv32-riscv64-shared` | simpleos-platform-team; template ownership inventory | Implement `scripts/check/check-riscv32-riscv64-template-ownership.shs`, then retain shared-path inventory and justified architecture-only leaves. |
| `simple-generated-vhdl-linux` | hardware-team; admitted Stage 4 generator and RTL tools | Run `scripts/check/run-riscv-gen2-hwir-qualification.shs --stage4-cli <simple> --stage4-provenance <provenance> --output-dir <dir>`, then `sh scripts/check/check-riscv-rtl-linux-smoke.shs --timeout=30`; retain generator hashes, RTL qualification, Linux boot, and `ls`. |
| `binary-size-go-parity` | performance-team; equivalent stripped programs | Run `RUNS=50 WORKERS=100 sh scripts/check/check-cross-language-perf.shs`, then implement the missing threshold validator `scripts/check/check-binary-size-go-parity.shs`; retain tool versions, hashes, and byte counts. |
| `interpreter-startup-parity` | performance-team; controlled cold/warm host | Run the same cross-language profiler, then implement `scripts/check/check-interpreter-startup-parity.shs`; retain raw samples, environment identity, statistics, and verdict. |
| `rust-go-benchmark-parity` | performance-team; semantic-equivalence oracle | Run the same cross-language profiler, then implement `scripts/check/check-rust-go-benchmark-parity.shs`; retain raw samples, statistics, and threshold verdict. |

Shared interfaces: `push_must_check`, `bootstrap_must_check`, and
`must_check_ledger`. Manual helpers: `step("Run the lightweight push
must-check")`, `step("Run the bootstrap must-check")`, and `step("Validate the
must-check ledger")`. No implementation placeholder may pass; use `fail(...)`.
