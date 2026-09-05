# System test plan: StarFive VisionFive 2 NVMe storage

Contract tests cover REQ-001/002 and NFR-004/007. Read-only live identification covers
REQ-003/009 and NFR-001/002/003/006/008. Explicit provision-live covers REQ-004..009 and
NFR-002..005/008.

Visible steps: Identify NVMe namespace; Initialize JH7110 PCIe host; Bind shared NVMe driver; Partition and format selected namespace; Mount filesystem; Verify write and read; Run ls on NVMe root.

Execution note: `--identify-live` must precede `--provision-live`. The latter
consumes the immutable receipt path, repeats read-only identification, rejects
any identity/image change, and requires exact receipt-bound authorization.
Linux-side identity capture may be retained as independent diagnostics but
cannot replace SimpleOS live evidence.

Current live verdict: BLOCKED until physical UART proof and exact identity cross-validation are collected in a
single production run. A contract PASS must never be reported as physical storage PASS.
