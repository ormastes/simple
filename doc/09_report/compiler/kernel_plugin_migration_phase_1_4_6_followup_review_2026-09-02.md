# Kernel Migration Phase 1/4/6 Follow-up Review

## Verdict

`STATUS: WARN`

- Phase 1: code/production reachability PASS; focused SPipe runtime BLOCKED.
- Phase 4: code/production reachability PASS; focused SPipe runtime BLOCKED.
- Phase 6: initial review FAIL; corrected code and shell authority PASS; focused
  SPipe/native runtime BLOCKED.

No helper-only or lexical check is counted as runtime evidence.

## Phase 1 — Typed-HIR ABI Digest

- `src/compiler/20.hir/abi_interface.spl:350` computes the digest exclusively
  from typed `HirModule` data and canonical SHA-256 framing. The module imports
  no environment, filesystem, process, logging, or runtime I/O owner.
- The production HIR driver calls the logging boundary in both streaming and
  ordinary lowering routes at
  `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:410` and
  `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:884`.
- The only production consumers of `hir_abi_interface_digest_v1` are the
  logging boundary and its two driver calls. No cache, admission, dispatch, or
  build decision reads the digest.
- `test/01_unit/compiler/interface_compat/compile_interface_spec.spl:236`
  drives source through the production parser and HIR lowerer. It proves body
  stability, append/rename/type/reorder sensitivity, and unresolved-type
  refusal. The retype scenario turns an encoder mutation that drops field type
  information red.
- Full driver log execution is not claimed because no admitted self-hosted
  runtime with `test` is available.

## Phase 4 — Canonical Provider Identity

- `src/compiler/90.tools/lint/lint_rule_api.spl:65` derives the host contract
  digest from canonical framed contract fields.
- `src/compiler/90.tools/lint/lint_rule_api.spl:77` derives each provider digest
  from the host contract digest plus its canonical rule identity under a
  separate domain.
- `src/compiler/90.tools/lint/static_rules.spl:44` recomputes the host contract
  and `src/compiler/90.tools/lint/static_rules.spl:60` independently recomputes
  each provider identity before dispatch.
- Production lint reaches the table through
  `src/compiler/90.tools/lint/_LintMain/lint_checks.spl:285` and
  `src/compiler/90.tools/lint/_LintMain/lint_checks.spl:429`.
- Negative tests reject a sibling provider digest, the exact host digest, a
  forged host digest, and duplicate production provider identities at
  `test/01_unit/compiler/lint/lint_rule_table_spec.spl:53`.

## Phase 6 — Explicit Compiler-Bound ABI Admission

The review found three silent `compat-deferred` defaults and an admission gate
that trusted a present `admission_identity` without recomputing it.

Corrections:

- `src/compiler/70.backend/backend/runtime_compiler.spl:73` now returns an error
  when `SIMPLE_ABI_POLICY` is absent or unknown. Runtime C defines are produced
  only after that production environment boundary returns an explicit policy.
- `scripts/check/lib/bootstrap-stage3/authority.shs:1967` and
  `scripts/check/lib/bootstrap-stage3/sanity.shs:255` no longer default absent
  policy to `compat-deferred`.
- `src/compiler/80.driver/driver_build/incremental.spl:303` recomputes the exact
  Stage-2 admission identity from candidate, source, runtime, tool, build args,
  sanity, receiver, and hosted-runtime evidence. All digests must be canonical
  lowercase SHA-256 values.
- `src/compiler/80.driver/driver_build/incremental.spl:335` binds admission to
  the running compiler executable digest, explicit policy, runtime ABI bits,
  immutable receipt identity, and full receipt digest. Missing or mismatched
  authority yields an uncacheable identity at the production caller; it never
  selects deferred or v1.

Mutation evidence:

- `test/01_unit/compiler/backend/runtime_compiler_spec.spl:16` invokes the
  production environment boundary and rejects absent/unknown policy.
- `test/01_unit/compiler/driver/native_cache_producer_identity_spec.spl:123`
  rejects changed admission identity, changed source evidence, a different
  compiler, duplicate fields, and non-canonical compiler digest.
- `test/01_unit/scripts/bootstrap_stage3_receipt_reuse_test.shs:116` invokes the
  real receipt writer and verifier with policy unset and proves both fail
  without publishing residue.

## Executed Evidence

- `sh test/01_unit/scripts/bootstrap_abi_policy_contract_test.shs`: PASS.
- `sh test/01_unit/scripts/bootstrap_stage3_receipt_reuse_test.shs`: PASS.
- Focused `git diff --check`: PASS.
- Focused shell syntax checks: PASS.
- Repository scan found no remaining production
  `${SIMPLE_ABI_POLICY:-compat-deferred}` default.

## Runtime Blockers

- `bin/simple` is the reduced pure-Simple bootstrap compiler and exposes no
  `test` command, so the focused SPipe specs cannot run through the required
  self-hosted tool.
- The isolated Stage3 wrapper and worker are terminal. Stage3 ended with
  `native-build worker exited with code 1`; no candidate or `provenance.env`
  exists.
- The retained `stage2-runtime-authority/simple` identifies itself as the Rust
  bootstrap seed. Repository policy forbids using it as test/runtime evidence.
- Therefore no Simple/SPipe runtime PASS or native qualification PASS is
  claimed by this review.
