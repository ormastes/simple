# Ubuntu43f Result predicate lowering

The completed Ubuntu43f/e589 attempts U43F-006, U43F-007, and U43F-011
include unresolved `is_ok`/`is_err` calls from process code. Their other
diagnostics are separate: Result payload/class provenance, process enum
constructors and comparisons, text methods, and the U43F-011 `smf_mmap_native`
dictionary receiver. This change does not claim to resolve those attempts.

Evidence index: `D:/dev/ubuntu43f-failure-catalog-20261003/evidence.json`.
Frozen source: `43f626850b6a5531e89110f75cd1eaedc24adcd1`.
Producer: `e58968bba401407bb04d6b581e62cf1dcf480847ec56338bb7a06ad4003283ff`.
Candidate base: `5daa48dfbf` on an isolated D worktree.

## Cause and change

MIR recognizes canonical `HirTypeKind.Result`, constructs `Ok` with tag 0
and `Err` with tag 1, and lowers Result unwrap operations. It had no lowering
for Result `is_ok()` or `is_err()`, so these calls reached unresolved-method
diagnostics despite a declared Result receiver.

A separate helper admits exactly these two zero-argument predicates on a
proven Result type with unresolved dispatch. Explicit instance, trait, UFCS,
or static method selections retain ownership even on Result storage.
It evaluates the receiver once, calls
`rt_enum_discriminant`, and compares to the appropriate canonical tag.
It does not unbox the payload, guess from method names, or take over custom
nominal methods. Unknown receivers and invalid arity retain ordinary error
handling. All non-predicate methods return from the helper after a constant
shape check; no host access or new runtime API is introduced.

The existing Result unwrap lowering uses the same `rt_enum_discriminant`
signature (i64 handle to i64 tag) and compares to 0/1. The native runtime
provider returns the stored `RtCoreEnum.discriminant` (or -1 for invalid
storage), so this is a discriminant check rather than payload truthiness.

## Regression and qualification

- `test/01_unit/compiler/mir/result_predicates_spec.spl` lowers real source
  through HIR/MIR and checks typed parameters, function-return provenance,
  same-name nominal method ownership, unsupported integer receivers, and
  wrong argument count, explicit method resolution precedence, exact receiver
  call count, equality operation, and the canonical tag constants.
- `test/01_unit/compiler/mir/fixtures/result_predicates_native.spl` checks
  all four combinations of Ok/Err and is_ok/is_err, four exact receiver
  evaluations, and custom methods. Oracle: exit 0 and stdout exactly
  `result-predicate-truth-table-pass` plus a newline. Failure exits 11–17
  identify the semantic condition without depending on assertion ABI.
- Static whitespace and generated-spec layout checks passed.
- Independent scoped source review accepted the initial helper; root review
  requested explicit-resolution precedence and MIR evaluation-count checks,
  which are included. This is draft source evidence, not executable PASS.
- Compiler specs, native fixture, and full compiler/lib/MCP/LSP verification
  are UNRUN. The Linux owner confirmed there is no qualified patched-candidate
  test runner yet; the old e589 producer would only provide baseline evidence.
- Queue the fixture after incorporating this reviewed source in the next
  pinned compiler candidate. No unreserved build or frozen-source edit occurred.

The shared method-call file is coordinated with the SDN/Identity enum owner
(unresolved-owner block) and LSP owner (primitive len/is_empty block). This
patch only adds the Result helper import and dispatch next to option lowering.
