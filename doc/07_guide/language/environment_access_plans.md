# Environment Access Plans

Production RT/HAL environment tests express host effects as a bounded ordered
`EnvAccessPlan`. The app I/O host is the sole executor. It validates the whole
plan before executing instructions sequentially and commits receipts in source
order; test leaves never perform physical effects themselves.

The closed v1 instruction set contains 24 kinds: environment read, host
identity, repository-file read, admitted-tool execution, hardware probe, four
socket lifecycle operations, device read/write, MMIO read/write, four IRQ
operations, six DMA operations, and monotonic clock read.

Tool execution uses a canonical pre-hashed path without `PATH` or a shell.
Repository reads require canonical containment and no-follow regular files.
Clock reads use the app time owner. Every socket, device, MMIO, IRQ, and DMA
operation requires a parent-supplied typed physical adapter whose identity and
bounds exactly match the plan. No ambient physical registry exists. Adapters own their handles and side effects;
instructions carry no pointers or file descriptors. This permits real sockets
and platform HAL owners without transferring mutable authority into a test.

An absent, schema-mismatched, unavailable, or too-narrow adapter fails closed
with an `Unsupported` receipt. The receipt names the missing prerequisite,
`environment-executor` owner, this canonical evidence artifact, and the exact
resume action. Output is truncated to the declared per-instruction bounds and
the parent hashes observations before publishing a receipt. Plans are bounded
to 1,024 instructions, 64 adapters/processes, and 64 MiB captured output.
