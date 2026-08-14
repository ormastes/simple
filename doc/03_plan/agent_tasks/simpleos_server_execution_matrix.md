# Agent tasks: SimpleOS server execution matrix

| Lane | Ownership | Exit |
|---|---|---|
| ARM QEMU | ARM image, VFS executable, HTTP/DB/persistence receipt | Real ARM receipt or exact owner-layer blocker |
| UNO Q CPU | Physical identity, safe deployment, filesystem server, CPU-only | Retained CPU receipt or exact board/port blocker |
| UNO Q GPU | Adreno/Vulkan device execution with server live | Retained device receipt or exact backend blocker |
| Linux perf | nginx/PostgreSQL/SQLite CPU/CUDA comparison, README | Fair report; up to three Pure-Simple fix cycles |
| Merge owner | Canonical state/plan/docs, static gates, integration | Clean linear reachable push |
| Final reviewer | Requirements, implementation and evidence audit | PASS or explicit REJECT findings |

UNO lanes serialize device access with `/tmp/unoq-server-matrix.lock`. The merge
owner alone edits canonical state and master plan. No lane commits.
