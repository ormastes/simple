# SimpleOS server execution matrix

Source: `test/03_system/os/server/simpleos_server_execution_matrix_spec.spl`

> Authored manual; uncredited. SPipe/docgen and runtime execution were not run
> because the current-source ARM compiler/sysroot/runtime prerequisites are
> unavailable. Storage admission and the QEMU executable preflight pass. This document records intended operator flow,
> not generated-manual provenance or a PASS.

## Purpose and acceptance boundary

This matrix requires current filesystem-launched server bytes and a retained
`SimpleOsServerExecutionReceiptV1`. A marker executable, hosted service, x86 or
Linux substitute, Rust seed, software GPU, missing receipt, or unavailable-row
skip fails closed. Mutable socket, database, and filesystem state remains owned
by one parent; device work crosses the boundary only as immutable input and a
validated bounded result.

## Preconditions

- Current source revision, executable SHA-256, and an opaque run-local image
  SHA-256 provenance. The hash may be retained; do not distribute the
  credential-bearing image itself or its credential bytes.
- Canonical ARM64 QEMU image/runtime or recoverable physical UNO Q SimpleOS
  runtime, as selected by the row.
- Persistent filesystem media, host-visible networking, and retained command,
  UTC timestamp, exit status, identity, and raw transcripts.
- A non-empty database credential file of at most 128 bytes supplied through
  `SIMPLEOS_SERVER_DB_CREDENTIAL_FILE`; it is staged as `/SYS/SRVDB.KEY`. Never
  put its bytes in a command line, log, protocol transcript, or receipt.
- Treat the generated disk image as ephemeral secret material: restrict access,
  exclude it from distribution/retained evidence, and securely destroy it after
  the same-image reboot probe.
- For GPU, physical Adreno/Vulkan identity plus submit, fence/completion, and
  device-origin readback. CPU rows must prove GPU libraries were not selected
  or loaded.

## Operator matrix

| Row | Visible flow | Required result | Current source/evidence status |
|---|---|---|---|
| ARM64 QEMU CPU (`qemu-arm64-cpu`) | **Boot ARM QEMU server executable** → **Serve a filesystem document over HTTP** → **Persist and reload a database value** | Filesystem-resolved current server, host HTTP bytes, durable value after fresh boot | Source prerequisites advanced: filesystem payload, VirtIO-MMIO NIC queues, bounded TTBR0-aware copy, capability-gated socket dispatch, FAT32 metadata sync, and VirtIO block FLUSH. Storage admission and QEMU executable checks pass. Runtime credit remains blocked by non-atomic FAT32 replacement, hosted DB runtime dependencies, and missing current-source ARM compiler/sysroot/runtime artifacts. |
| UNO Q CPU (`unoq-cpu`) | **Launch UNO Q server executable** → HTTP/DB restart probes → **Verify UNO Q CPU-only path** | Physical receipt and no GPU selection/loading | Identity-only Debian/Adreno evidence exists. The physical SimpleOS runtime and filesystem server executable are absent; the current cross-build/runtime blockers remain open. No row credit. |
| UNO Q GPU (`unoq-gpu`) | **Launch UNO Q server executable** → live server probes → **Verify UNO Q GPU-accelerated path** | Physical Adreno/Vulkan submit, completion and device readback while the server remains live | Physical hardware identity is known, but the canonical SimpleOS evidence provider is absent. No submit/readback or server-liveness credit. |
| Linux CPU | Equivalent Simple/nginx HTTP and Simple/PostgreSQL/SQLite DB operations | Fixed affinity, concurrency, durability, dataset, warmup, samples, p50/p95, throughput and peak RSS | Fresh Simple HTTP did not bind a listener; DB validation hit an invalid array-handle ABI. Historical non-equivalent timings are diagnostic only. |
| Linux optional GPU | Same live server workload plus one named immutable compute stage | Parent-owned socket/DB/filesystem state; optional CUDA absent from CPU row | No admitted live comparison or optional-CUDA receipt. Missing helper fails explicitly. |

## Executable helper contract

The executable spec freezes `arm_qemu_server_fixture`,
`uno_q_server_fixture`, `expect_http_file`, `expect_db_reboot`,
`expect_cpu_mode`, and `expect_gpu_receipt`. Every unresolved helper calls
`fail(...)`; the Linux and deliberate-red rows also fail explicitly until live
owners exist. No scenario is skipped and there is no placeholder assertion.

## Evidence, provenance, and limitations

Expected retained evidence is raw log, redacted protocol transcript, executable
and image SHA-256 values, target identity, source revision, exact command, UTC time, and exit
status. Credential bytes are explicitly excluded and must be redacted if an
external client echoes them. This authored mirror has no generated score, runtime transcript, or
review credit. Run SPipe/docgen only after the pure-Simple current-source ARM
compiler/sysroot/runtime admission blockers are cleared.

The host staging buffer is explicitly wiped after its image copy. Target-side
immutable byte/text copies currently lack guaranteed secure zeroization; this is
an open release blocker, not a confidentiality claim.
