# Container/GPU 8K80 completion requirements

The user selected both non-physical lanes: native DrawIR and strict semantic
GPU production. Physical display work remains separately tracked.

- **REQ-R8KC-001:** Build A4 with a source-matched, admitted non-seed
  pure-Simple compiler and execute the produced artifact directly.
- **REQ-R8KC-002:** The A4 receipt must bind 7680x4320, 20 revisions, 256x128
  damage, exact command counts, p50/p95, RSS, checksum, readback source/count,
  mismatches, completion, and fallback; p95 must be <=12,500,000 ns.
- **REQ-R8KC-003:** Produce a changing Web/GUI/WM semantic revision through
  canonical DrawIR and Engine2D using strict Vulkan selection and device-origin
  readback; reject software fallback and CUDA-only buffer-fill substitution.
  The producer uses one untimed warmup and 60 timed changing revisions.
- **REQ-R8KC-004:** Emit `drawir_receipt`, `producer_receipt`, and
  `aggregate_receipt` with `pass`, `failed`, or `blocked` status and immutable
  source/artifact/workload/device correlation fields.
- **REQ-R8KC-005:** Aggregation must reject missing, stale, malformed,
  cross-workload, seed/interpreter/stub/fallback, unknown-completion, zero-RSS,
  zero-checksum, timed-readback, and over-budget evidence.
- **REQ-R8KC-006:** Without a valid physical A6/A8 receipt, the aggregate must
  report `blocked-physical`, never campaign PASS. TODO684/TODO685 remain open.
- **REQ-R8KC-007:** The A6 software producer must lower the same changing Web
  semantics as A5, submit and visibly present through one returned Engine2D
  owner, time no host readback, and retain an untimed device checksum oracle.
  Its receipt must say device-window presentation is not physical scanout
  capture; A6 promotion still requires independent same-run capture/readback.
