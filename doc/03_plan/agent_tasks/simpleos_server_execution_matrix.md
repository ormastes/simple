# Agent tasks: SimpleOS server execution matrix

| Lane | Ownership | Exit |
|---|---|---|
| ARM QEMU | ARM image, VFS executable, HTTP/DB/persistence receipt | Real ARM receipt or exact owner-layer blocker |
| UNO Q CPU | Physical identity, safe deployment, filesystem server, CPU-only | Retained CPU receipt or exact board/port blocker |
| UNO Q GPU | Adreno/Vulkan device execution with server live | Retained device receipt or exact backend blocker |
| Linux perf | nginx/PostgreSQL/SQLite CPU/CUDA comparison, README | Fair report; up to three Pure-Simple fix cycles |
| Merge owner | Canonical state/plan/docs, static gates, integration | Clean linear reachable push |
| Final reviewer | Requirements, implementation and evidence audit | PASS or explicit REJECT findings |

### QRB2210/Imola boot-owner implementation order

1. Obtain the authoritative Arduino/Qualcomm board revision, signed boot-chain
   format, partition/download manifest, rollback policy, and factory recovery
   procedure. Record hashes and licensing; do not infer partition names.
2. Add a pure, read-only admission owner for those manifests: exact board ID,
   signature/provenance, anti-rollback value, payload/rootfs hashes, and recovery
   image must all be present before any mutation can be requested.
3. Add a separate destructive download executor only after explicit user
   authorization. It must hold `/tmp/unoq-server-matrix.lock`, verify EDL
   `05c6:9008`, snapshot/verify recovery material, use the vendor-supported
   flasher, and fail closed before the first write on any mismatch.
4. Boot current SimpleOS from the authorized slot/carrier, prove SimpleOS
   identity before filesystem/server checks, and retain the frozen receipt.
   Debian/ADB observations remain readiness diagnostics only.

Current status: blocked before step 2 because the public authoritative signing,
partition, rollback, and custom-OS recovery contract is unavailable. No safe
source-only downloader is implementable from the present evidence.

UNO lanes serialize device access with `/tmp/unoq-server-matrix.lock`. The merge
owner alone edits canonical state and master plan. No lane commits.
