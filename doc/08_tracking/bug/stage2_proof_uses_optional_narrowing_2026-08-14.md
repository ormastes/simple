# Stage 2 loses `HirContractBlock` type at optional narrowing

Date: 2026-08-14
Status: FIX IMPLEMENTED; current-head bootstrap verification pending
Owner: compiler HIR lowering / optional narrowing
Source authority: `0669f1b8d33f9c0d34afeed7f0b0c1b1f4bc7815` plus working fix

## Failure

A fresh full bootstrap completed publication of the Rust bootstrap tuple, then
failed current-head Stage 2 with exit 1. HIR lowering inferred the narrowed
`HirContractBlock?` payload as `ANY` at two `proof_uses` field reads:

- `src/compiler/50.mir/verification_contract_bridge.spl`, function
  `verification_contract_from_mir_v1`
- `src/compiler/70.backend/backend/lean_backend.spl`, function
  `function_contract_from_hir`

The fix gives each optional payload an explicit `HirContractBlock` binding
before any field read. No Rust/runtime fallback implements this behavior.

## Retained evidence

- Driver: `build/restart13-bootstrap/driver-cycle3.log`, SHA-256
  `ba5ffd0e101a8e40e0613b04e2d6ef84dd9cd3ffbb82330e12137d8d6f108f90`
- Stage 2 log:
  `build/restart13-bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`,
  SHA-256 `f09ebebcd6978097c00259caf442662329b89da65085d79d440ecb26ed0aaa27`
- Progress: `build/restart13-bootstrap/progress-cycle3.log`, SHA-256
  `12fe5dcbae46d2db398bc1c448e52a24d48d270e95c95dd4b1c0f3f56a3664dd`
- Exit status: `build/restart13-bootstrap/driver-cycle3.exit` (`2`; wrapper
  rejects unavailable Stage 4 after the Stage 2 child exits 1)

## Unblock condition

In a fresh capped verification session, reuse the published bootstrap tuple and
cache, rebuild Stage 2 once, and require both owner files to lower without an
`ANY proof_uses` diagnostic. Continue through provenance-verified Stage 3 and
Stage 4 before executing mission-critical SSpec or docgen.
