# Agent tasks: StarFive VisionFive 2 NVMe storage

- Research lanes:
  - common NVMe protocol and filesystem behavior,
  - JH7110 PCIe host/resource ownership,
  - Linux-side installed SSD identity capture for boot-safe provisioning.
- Merge owner: primary Codex agent.
- Implementation:
  - complete identity-bound authorization (serial+NSID+LBA geometry+hashes),
  - add lightweight in-use/boot-source exclusion checks,
  - normalize host-resource admission with minimal DT variation support,
  - finish mounted/in-use/live read/write evidence in provision path,
  - keep shared PCI/NVMe logic host-neutral and board-agnostic.
- Final reviewer: `$verify`; physical PASS requires retained UART + Linux identity + storage receipts.
