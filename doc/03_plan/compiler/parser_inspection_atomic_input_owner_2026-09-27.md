# Atomic input owner for parser binary inspection

Status: implementation plan for selected EODL REQ-016 / NFR-012; no process
inspection authority is implemented by this document.

## Boundary to build

Use the existing native owned-process engine for nonblocking stdin writes and
concurrent stdout/stderr drain, and the V4 executable/cwd pin, exact argv/env,
deadline, ticket, and two-phase collection rules. Define a new versioned
inspection request/receipt rather than changing V4's fixed 64-word packet or
accepting V3 and V4 receipts as if they came from one process.

The start call receives `(executable_pin, cwd_pin, canonical_request,
input_bytes)` once. Before creating a child it must:

1. Validate length against the selected 16 MiB input bound and all request,
   output, deadline, environment, and slot bounds without arithmetic wrap.
2. Copy the bytes into owner storage and compute digest/count from that copy.
   Bind digest/count to the canonical request and tool/argv/environment/pin
   identities. Reject a mismatch before process creation or token minting.
3. Reserve a bounded process slot and stdin/stdout/stderr/exec pipes as one
   rollback-safe transaction. A failed reservation or pipe setup leaves no
   child or retained lease.
4. Spawn only the pinned image with the exact declared environment and cwd.
   The child never sees a live caller buffer. Expose an opaque lease only after
   the native owner has retained the copied input and process identity.

The poll/collect owner must pump stdin and both captures fairly under one
bounded wall/cleanup budget. It records accepted bytes, actual written bytes,
write error, stdin closure, stdout/stderr seen and kept bytes, truncation,
child exit/signal, identity revalidation, process-group cleanup, and reap.
Only an exact full write **and** close plus complete bounded captures and reap
can produce an authoritative terminal receipt. EPIPE, zero-progress writes,
early child exit, timeout, cancellation, overflow, and failed cleanup produce
explicit non-authoritative receipts. A lease remains retained until terminal
collection is acknowledged or a cleanup failure is quarantined.

The compiler tool owner validates the exact readobj and objdump policies
against the native owner's immutable process facts, then joins their captured
outputs with `parser_external_inspection_terminal_join_v2`. No constructor
that accepts a caller-provided `ParserExternalInspectionPinnedCaptureReceiptV1`
may mint the token. The compiler-facing start/join API must consume or borrow
the opaque native lease, so a copied receipt cannot forge completion.

## Source changes in dependency order

| Step | Owner | Proof before next step |
|---|---|---|
| 1. Versioned request/receipt schema | `src/lib/common/process/`, native codec | canonical round trip; malformed, duplicate, oversized and digest-mismatch rejection |
| 2. Native start and pump | `src/runtime/runtime_process_owned.c` | pinned exact-env child hashes stdin; simultaneous large stdout/stderr cannot deadlock |
| 3. Retained Simple process façade | `src/lib/nogc_sync_mut/io/process_ops.spl` | opaque lease, exact collection/ack, no raw process shortcut |
| 4. Compiler inspector owner | `src/compiler/80.driver/parser_external_inspection_tool_owner_v1.spl` | two tools, distinct argv policy, same input identity, exact output and terminal join |
| 5. Product admission | EODL SPipe and compiler/MCP gates | negative matrix and representative binary inspection run on admitted self-hosted runtime |

## Acceptance matrix

- Same immutable binary input reaches both pinned tools; their independently
  observed input hash/count equals the owner-bound request. Mutating the
  caller's source array after start cannot alter either child input.
- A child that writes to both output streams while reading input larger than
  pipe capacity completes without deadlock. Captures are bounded and exact.
- Each failure listed above emits a stable reason and keeps inspection token
  issuance at zero. Wrong or stale executable/cwd pin, argv, environment,
  process generation, or receipt digest also keeps issuance at zero.
- Repeated valid inspection reuses no process authority across generations;
  release drains or quarantines every retained lease. Cold help/version paths
  start no inspector process.
- Measure warm/cold latency, max RSS, and input/capture bytes on named fixtures
  against the selected NFRs. Synthetic facts never count as native evidence.
