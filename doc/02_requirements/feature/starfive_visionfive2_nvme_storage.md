# StarFive VisionFive 2 NVMe storage requirements

- REQ-001: Discover JH7110 PCIe1 resources from the preserved, validated DTB.
- REQ-002: Keep PCI enumeration, NVMe protocol, GPT, FAT32, and VFS host-neutral.
- REQ-003: Identify controller and namespace without issuing writes.
- REQ-004: Require destructive authorization bound to serial, NSID, capacity, identify hash, and image hash.
- REQ-005: Create and validate aligned primary and backup GPT metadata for one dedicated partition.
- REQ-006: format that partition as FAT32 and mount it at `/nvme`.
- REQ-007: Write, flush, unmount, remount, and verify payload hash.
- REQ-008: Execute a command-correlated VFS `ls /nvme` showing the persisted file.
- REQ-009: Retain immutable build, identify, authorization, provision, and UART receipts.
