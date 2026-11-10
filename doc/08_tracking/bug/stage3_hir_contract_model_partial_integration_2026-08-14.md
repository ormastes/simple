# Stage 3 HIR contract model partial integration
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: FIX IMPLEMENTED; native verification pending
- Date: 2026-08-14
- Owner: compiler HIR model/lowering

## Failure

A current-source pure-Simple Stage 3 build reached all 616 parsed sources and
failed closed in HIR lowering:

```text
[ERROR] phase 3 FAILED
unresolved name: HirContractClauseKind
unresolved name: HirContractOutcome
```

The diagnostic associated the poisoned module with
`src/std/nogc_sync_mut/io/sffi_common.spl`, but that module does not reference
either name.  The authoritative missing definitions were in
`src/compiler/20.hir/hir_definitions.spl`: verification MIR/backend consumers
had landed while the corresponding HIR contract types and `HirFunction` field
had not.

## Fix

Restore the typed `HirContractClauseKind`, `HirContractClause`,
`HirContractOutcome`, and `HirContractBlock` model; retain an optional
`HirFunction.verification_contract`; initialize it explicitly in both HIR
lowering constructors; preserve it through semantic resolution; and remove the
fragile positional `HirFunction` pattern used only to read `is_extern`.

## Evidence and unblock condition

- Failed build log: `build/native_probe/stage3-fresh/build.log` (exit 1).
- The first cache-preserving retry no longer reported the missing contract
  names and was observed externally terminated. Its retained log proves only
  that no compiler error or candidate was emitted; it does not retain the exit
  code or sampled RSS. This is not proof of a second compiler defect and not
  proof that the HIR fix passed end to end.
- Exact source check/regression and a fresh pure-Simple Stage 3 build must pass
  without these unresolved names.
- The produced Stage 3 must then pass the existing hello and module-qualified
  field-layout probes.  Rust-seed execution is not acceptance evidence.


---

## 2026-11-10 (p0-hir-verify lane, Windows worktree, seed-smoke) — FIX RE-CONFIRMED PRESENT; RUNTIME CLOSURE STILL BLOCKED

Lane: `work/p0-hir-verify-20261110` on `origin/release/1.0.0` (includes Nil-singleton PR #8142).
Runtime: `bin/simple.exe` Rust seed v1.0.0-rc.1, `--mode=interpreter`; seed-smoke only.

### Static re-confirmation of the fix (current source, all five elements)

1. `src/compiler/20.hir/hir_definitions.spl:123-143` — typed model present:
   `enum HirContractClauseKind` (Requires/StatePredicate/EnsuresNormal/EnsuresError/Decreases),
   `struct HirContractClause`, `enum HirContractOutcome` (Plain/Result), `struct HirContractBlock`.
2. `hir_definitions.spl:102` — `HirFunction.verification_contract: HirContractBlock?` retained.
3. Both HIR lowering constructors initialize it explicitly:
   `hir_lowering/_Items/declaration_lowering.spl:176` (`verification_contract: nil,`) and
   `:541`/`:661` (`val verification_contract = self.lower_verification_contract(fn_.contract,
   return_type)` then `verification_contract: verification_contract,`).
4. Preserved downstream: generated codec `hir_codec.spl:5606,5749-5789` encodes/decodes the
   field; `hir_reference_snapshot_v1.spl:477` and `archive/tldr_function_header_v1.spl:124`
   retain it; `portable_body_semantics.spl:127` gate-checks it.
5. The fragile positional pattern is gone: the codec reconstructs `HirFunction` with named
   fields (`hir_codec.spl:5789`); no positional `HirFunction` destructure remains in `20.hir`.

Lowering owner `hir_lowering/_Items/verification_contract_lowering.spl` lowers all four clause
kinds plus `decreases` and selects Plain/Result outcome (`:42-73`), re-exported through
`hir_lowering/items.spl:18`.

### Executable focused verification (seed-smoke)

`test/01_unit/compiler/bootstrap/verification_contract_proof_uses_bootstrap_spec.spl`
(3 examples covering the parser ContractBlock/ContractClause owners, the lowering owner
wiring, and the MIR/Lean bridge preservation): **3/3 PASS, exit 0**.

### Still blocked (unchanged)

- Exact source check `SIMPLE_LIB=src bin/simple check src/compiler` — the `check` pipeline
  refuses the Rust seed: "ERROR: no admitted cached self-hosted check worker artifact is
  available ... deploy bin/release/<triple>/simple or set SIMPLE_BINARY" (verified
  path-independent, including single-file `check src/compiler/20.hir/hir_definitions.spl`).
  Needs an admitted pure-Simple binary.
- Executable contract-syntax parse/lower/run under the seed — BLOCKED by seed grammar, not
  by the fix: the seed rc.1 frontend rejects the current `in:`/`out(ret):` clause surface
  (`expected Newline, found Identifier` at the clause's first operand; minimal fixture
  `build/review/fixtures/contract_min_in_out.spl` fails the same way). The seed predates the
  contract-clause syntax entirely, consistent with this doc's "Rust-seed execution is not
  acceptance evidence."
- Fresh pure-Simple Stage 3 build + hello + module-qualified field-layout probes — needs the
  canonical bootstrap transaction (no admitted producer in this lane; same gate as
  stage3_current_source_hir_rss_termination_2026_08_14).

Status: FIX IMPLEMENTED re-confirmed on current source with focused spec green; native
verification still pending the admitted pure-Simple CLI.
