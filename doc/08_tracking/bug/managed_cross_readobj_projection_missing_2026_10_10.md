# Explicit managed cross-runtime inspector capture

Status: capture-only repair. Cross-target compiler admission and apps are unqualified.

The cross archive consumer being qualified separately requires a pinned llvm-readobj. The existing authority snapshot could not emit that role. However, the current release managed-tool decoder accepts exactly eight roles. Automatically adding an installed inspector would break ordinary release consumers.

The snapshot therefore preserves its eight-role default even when llvm-readobj is installed. A caller may explicitly request the ninth role with SIMPLE_MANAGED_CROSS_ARCHIVE_INSPECTOR=1 alongside SIMPLE_MANAGED_NATIVE_TOOLS=1. Unset or empty inspector option preserves the default. Other values reject capture; requesting an inspector without managed mode, with no discoverable inspector, or with a failing version probe rejects snapshot publication. The selected executable follows the existing LLVM resolver and canonical path/hash/version capture.

Opt-in requires a separately reviewed consumer decoder that supports the optional role; current release consumers do not. This producer option is not a claim that release supports cross-target admission. Do not bypass consumer validation, hand-author receipts, or enable the option for legacy consumers. No live frozen compiler source or active authority cache is changed by this patch.

The focused shell regression invokes the real snapshot function with isolated executable-version fixtures and actual hashing. Its seven cases cover installed-inspector default8, opt-in selected path/hash and nine roles, changed-byte hash, failing version probe, requested missing tool, invalid option, and unmanaged-mode rejection. These fixtures test discovery, byte identity and fail-closed publication only; they do not prove LLVM tool semantics, archive validation, or app qualification.

Verification: `sh test/01_unit/scripts/bootstrap_managed_readobj_authority_test.shs` passed all seven cases once on Linux after the opt-in revision. Actual output: `PASS: cases=7 legacy installed default8, requested identity9, changed hash, broken/missing/invalid/unmanaged rejection`. No bootstrap or native app build was launched.
