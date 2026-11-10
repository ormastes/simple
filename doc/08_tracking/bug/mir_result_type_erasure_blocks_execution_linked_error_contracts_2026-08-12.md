# MIR Result execution refinement is incomplete for error contracts

Status: open — Formal Verification 2.0 P0

## Evidence

The original defect erased `HirTypeKind.Result<T, E>` to `MirType.i64()`.
FV2 now retains `MirTypeKind.Result(ok, err)`, serializes both payload types,
classifies the VIR representation as exact when both payloads are closed, and
maps the native ABI explicitly to the established tagged i64 handle.

Typed `Ok`/`Err` construction now keeps the Result destination type and literal
variant identity on the actual `rt_enum_new` MIR call. The Lean backend lowers
those executed calls to `Except.ok`/`Except.error` and rejects malformed or
dynamic discriminants. The Lean backend also recognizes the canonical pure
`?` CFG only when discriminator, literal Err key, branch condition, unchanged
Err return, and Ok payload extraction all agree, lowering it to an exact
`Except` match. Exhaustive shallow `Ok(payload)`/`Err(error)` matches now carry
a typed ghost MIR witness and lower only after the backend independently
validates both literal comparison predecessors, connected fallthrough chain,
payload extractions, merge assignments, and impossible edge. Nested/deep or
stateful matches and nontrivial payload bridges remain open.

## Required fix

Complete tagged normal/error propagation beyond the bounded pure `?` and
shallow exhaustive-match shapes, return, deep matching, interpreter behavior,
general structured-CFG Lean semantics,
and backend refinement. Prove that the
logical `Except err ok` value refines the deployed tagged handle and that every
actual translated return path selects the corresponding constructor.

## Unblock condition

A deliberately incorrect implementation that returns `Err` where the contract
requires `Ok` must fail its generated theorem, while correct normal and error
implementations compile and their transitive axiom audits close.

## Triage 2026-11-11 (p3-compiler4 lane, batch 4 row 8) — BLOCKED (out of lane grant; stays OPEN)

FV2.0 progress described in this record is real in source at this lane's base:
`src/compiler/50.mir/mir_types.spl:193-196,249,280` retains
`MirTypeKind.Result(ok, err)` with exact payload types and the tagged 8-byte
native ABI; the Lean backend and VIR exactness work land under
`src/plugins/backend_lean/` and `50.mir/verification_ir.spl`.

The required fix, however, is Formal-Verification-2.0 research work — complete
tagged normal/error propagation beyond the bounded shapes, generated Lean
theorems, and transitive axiom audits (this record's unblock condition). Its own
FV specs say they "cannot be admitted until a self-hosted full CLI is
available" (e.g. `test/00_formal_verification/compiler/three_payload_compile_refinement_spec.spl`).
This lane carries no FV/Lean toolchain grant and no entry-closure native-build
grant.

Exact grant command for the owning lane:
`SIMPLE_LIB=src bin/simple test test/00_formal_verification/compiler/ --mode=interpreter`
under an admitted self-hosted full CLI with the Lean toolchain on PATH, plus a
negative-test run proving a deliberately Err-returning implementation fails its
generated theorem (this record's unblock condition).
