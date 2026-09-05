# NFR: SimpleOS server execution matrix

- NFR-001 (provenance): every credited run records source revision, target
  identity, executable/image hashes, command, UTC time, exit status and output.
- NFR-002 (ownership): one parent owns mutable server, DB and filesystem state;
  child/device work receives copied, frozen or handle-bound input and returns a
  bounded encoded result for deterministic validation and commit.
- NFR-003 (safety): physical-board work is recoverable and scoped; no firmware,
  root filesystem, partition or boot-chain overwrite is permitted.
- NFR-004 (benchmark fairness): report CPU affinity/count, concurrency, payload,
  data set, warmup, sample count, durability semantics, p50/p95, throughput and
  peak RSS. Non-equivalent rows must be labeled.
- NFR-005 (optional GPU): CPU mode must not select or load CUDA/Vulkan. GPU mode
  must prove device, submission, completion and result readback.
- NFR-006 (convergence): each criterion runs once after implementation and each
  failing feature receives at most three measured fix cycles.
- NFR-007 (architecture): optimization preserves public behavior, ordering,
  errors and persistence formats; Pure-Simple owners remain authoritative.
