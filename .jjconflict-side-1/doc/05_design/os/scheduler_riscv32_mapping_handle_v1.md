# RV32 scheduler mapping handle v1

Status: implemented as an unverified ownership prerequisite; it does not make
RV32 tasks runnable.

## Contract

`TaskControlBlock` ABI revision 3 appends a two-scalar opaque locator. The
locator names a bounded slot and its nonzero generation. It contains neither
the Sv32 root lease nor the executable-authority mapping-pin transaction.

The loader's serialized RV32 mapper remains canonical owner of the root,
mapped frames, destruction receipt, and registry pin transaction. The locator's
slot/generation representation is intentionally compatible with that bounded
owner, but this phase exposes no constructor for a present locator: the mapper
does not yet have an owner-consuming transfer that invalidates the preparation
receipt and supplies retryable task-bound terminal/reap operations.

All existing TCB constructors install the absent locator. Fork deliberately
does not copy a parent's locator. Legacy exec rejects a present locator before
side effects because the required two-image owner transaction does not yet
exist.

## Explicit exclusions

- No SATP activation or raw root extraction.
- No scheduler publication/readiness transition.
- No exit/reap wiring or mapping destruction through the locator.
- No mapper-to-scheduler bind; all constructors produce the absent locator.
- No claim of RV32 filesystem launch or QEMU success.

The next integration must add an owner-consumed mapper-to-scheduler transfer
that invalidates the raw preparation receipt, publish only after TCB insertion,
define retryable terminal/reap ordering, and make unlock failure return durable
ownership rather than strand a bound slot.
