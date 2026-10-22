# Native batch bisect accepts relabelled compile receipts

Canonical ID: `native_batch_bisect_receipt_authority_2026_10_11`.
GitHub: [#3111](https://github.com/ormastes/simple/issues/3111).
Status: OPEN; isolated metadata controls pass, independent repair review and
current merged producer/runtime qualification pending. Native execution UNRUN.

On merged source tree `9a95f2ae00ec3080ef9bbfaf9508e8a8d4fc2c56`,
`scripts/bootstrap/native-batch-bisect.pl::validate_pass` checks adjacent build
labels against the lane but ignores the verified result's build digest and
backend, compiler, workspace and runtime capsule identities. An LLVM result
with unchanged manifest/native artifacts can be relabelled into a Cranelift
lane by editing only adjacent build.env. Prior PASS reuse invokes the same
weak validator. This is compile-evidence authority failure, not a compiler
codegen observation.

The repair uses `NativeAdapterEvidence::previous_build_evidence` to validate
strict build schema, original build digest, all result identity fields and the
reviewed stable lane. Initialization requires reviewed runtime capsule identity
and compares it to the initial build. Missing runtime authority in old states
requires explicit migration; there is no permissive fallback or new PASS.

Reproduction controls: `scripts/bootstrap/tests/native-batch-union-cli-test.pl`.
Fifty-four synthetic coordinator assertions passed once, including matching
receipts, adjacent build relabelling with original LLVM result/digest, five
result identity mismatches, missing schema/hash/runtime, self-consistent wrong
runtime, swapped binaries and unchanged survivor union behavior. Synthetic ELF
headers are validation fixtures; they were never compiled or executed and
prove no compiler/native/bootstrap coverage.

Evidence: `build/native_probe/phase3-whole-20261011-c06/reviews/native-batch-authority-child-9a95/`
contains exact parent/file/patch bindings and synthetic-control-receipt.json.
Full merged-source/native/Phase3 acceptance remains pending.
