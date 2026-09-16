# Must-check broad outcomes remain pending

## Status

Open. These outcomes are intentionally represented as `todo` in
`config/check/must_check_gates.sdn`; TODO is debt, never success. The bootstrap
runner must preserve them until the evidence below exists and passes.

## Gap inventory and unblock evidence

| Gate ID | Current gap | Required owner / unblock evidence |
|---|---|---|
| `web-server-gpu-nginx` | No retained GPU-offload and nginx-comparable throughput receipt | Web/server owner: identical-request correctness plus reproducible CPU/GPU/nginx benchmark artifacts |
| `db-server-gpu-sql` | No retained GPU database-logic and PostgreSQL/MySQL parity receipt | Database owner: result-equivalence suite plus reproducible throughput/latency artifacts |
| `simpleos-sbc-qemu-ls` | No paired physical-SBC and matching-QEMU boot/`ls` receipts | SimpleOS board owner: board identity, image hash, serial logs, QEMU log, and matching filesystem result |
| `simpleos-clang-hello` | No in-guest clang filesystem compile/run receipt | SimpleOS toolchain owner: compiler identity, source hash, executable hash, stdout and exit status |
| `simpleos-simple-toolchain` | No in-guest Simple compiler/interpreter/loader execution receipt | Compiler + SimpleOS owners: provenance-bound binaries and hello build/run logs for every path |
| `simpleos-server-executables` | No in-guest web/database server executable receipt | Server + SimpleOS owners: executable hashes, bounded launch/readiness/request/stop logs |
| `riscv32-riscv64-shared` | RV32/RV64 template ownership has not been audited | RISC-V owner: path inventory proving shared template ownership and justified architecture-only leaves |
| `simple-generated-vhdl-linux` | No generator provenance plus Linux boot/`ls` receipt | Hardware owner: Simple generator input/output hashes, synthesis/simulation evidence, boot log and `ls` output |
| `binary-size-go-parity` | No comparable retained Simple-vs-Go size measurement | Performance owner: equivalent programs, tool versions, strip settings, artifact hashes and byte counts |
| `interpreter-startup-parity` | No controlled Python/Bun/Go startup comparison | Performance owner: cold/warm methodology, raw samples, environment identity and threshold verdict |
| `rust-go-benchmark-parity` | No representative Rust/Go benchmark comparison | Performance owner: semantic-equivalence oracle, raw samples, statistics and threshold verdict |

## Guard location

The authoritative rows are in `config/check/must_check_gates.sdn`; their live
state is written to `doc/08_tracking/check/must_check_db.sdn`. Removing a row,
changing it to `pass` without bootstrap-owned evidence, or treating TODO as
success is a release-blocking defect.
