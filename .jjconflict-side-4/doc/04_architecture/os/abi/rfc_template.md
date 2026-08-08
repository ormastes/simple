# SimpleOS ABI Change RFC — Template

Copy to `doc/04_architecture/os/abi/rfc_<slug>.md`. A00 is the only approver;
no direct edits to frozen owners listed in `src/os/kernel/abi/abi_v1.spl`.

## Motivation
What breaks or is blocked without this change. One paragraph.

## Wire / surface change
Exact type, constant, or message-shape delta. Before → after.

## Compatibility
Version negotiation impact; which consumers must rebuild; migration window.

## Security effect
Rights amplification risk, new attack surface, audit-label changes.

## Tests
The contract/integration specs that prove the change (paths).

## Migration
Shim (with deletion condition) or hard cutover; old-path deletion commit plan.
