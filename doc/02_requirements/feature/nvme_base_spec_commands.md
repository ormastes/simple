# NVMe Base-Spec Command Requirements

The selected baseline is the must-have NVMe command floor requested for
production firmware evidence.

- REQ-001: Identify Controller and Identify Namespace must report usable controller and namespace data.
- REQ-002: IO completion and submission queues must support legal create/delete order and reject missing or busy queue bindings.
- REQ-003: Read, Write Zeroes, DSM Trim, and Flush command semantics must pass the firmware self-checks.
- REQ-004: Get/Set Features, Get Log Page, Format NVM, and firmware command guards must pass.
- REQ-005: Reserved-field, namespace, Abort, and backpressure guards must fail closed.

