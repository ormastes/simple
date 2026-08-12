# Locked Commit.Retire Observational Aspects

**Executable companion:** `test/01_unit/compiler/50.mir/hwir_commit_retire_aspect_spec.spl`

## Purpose and scope

This focused unit specification checks locked, typed observational attachment
at the stable `commit.retire` HWIR node of the bounded retirement composition.
It checks that an absent observer is structurally zero-cost, that ordered input
produces a stable weave receipt, and that observations retain the architectural
composition rather than replacing its bindings or producer ports.

## Scenarios

1. Apply an absent observer plan to a typed RV32 retirement composition.
2. Attach locked lineage and valid receipt observations to a typed RV64
   composition and compare order-independent weave hashes.
3. Reject a foreign target node and a receipt observation with the wrong width.

## Requirement traceability

- REQ-FV2-011 — the lock, exact join point, introduced observation ports, and
  weave identity are explicit.
- REQ-FV2-015 — the bounded check is anchored to canonical typed HWIR
  retirement semantics and its RVFI-facing observation seam.
- REQ-FV2-019 — foreign and mistyped observations fail closed.

## Evidence boundary

This is a typed composition and observational-weave unit test. It does not
prove an architectural retirement implementation, generate RVFI, run Sail or
riscv-formal/SBY, emit RTL, perform synthesis equivalence, or support an
unqualified verified-hardware claim.
