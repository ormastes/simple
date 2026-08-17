# System test plan: StarFive VisionFive 2 NVMe storage

Contract tests cover REQ-001/002 and NFR-004/007. Read-only live identification covers REQ-003/009 and NFR-001/002/003/006/008. Explicit provision-live covers REQ-004..009 and NFR-002..005/008.

Visible steps: Identify NVMe namespace; Initialize JH7110 PCIe host; Bind shared NVMe driver; Partition and format selected namespace; Mount filesystem; Verify write and read; Run ls on NVMe root.

Current live verdict: BLOCKED because UART is silent and no exact NVMe identity receipt exists. A contract PASS must never be reported as physical storage PASS.
