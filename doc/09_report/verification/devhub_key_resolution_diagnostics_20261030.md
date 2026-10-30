# DevHub key-resolution diagnostic evidence

Status: BLOCKED; production Messenger database acceptance remains failing.
Owner: Codex Astra. Source base: `7d0c0219cd2` plus the diagnostic fixture edit.
No production source repair is claimed.

The previously supplied Phase 2 producer remains unchanged, SHA256
`13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`.
Authority and limits are recorded in
`devhub_phase2_workarounds_20261027.md` and
`../../05_design/devhub_secured_sqlite_phase2_solution_20261027.md`.
These are scoped native fixture results, not Stage 4, SSpec, or release evidence.
Builds used the existing `build/devhub-completion/native-build-msvc.ps1`, LLVM,
Windows native provider roots, and the existing real memory-headroom object.
No compiler rebuild, Rust seed substitution, cache deletion, or manual build
restart occurred. Automatic MIR worker refusal followed by unsharded fallback
was observed; both retained builds eventually exited 0.

| Attempt | Result | Artifact SHA256 |
| --- | --- | --- |
| Historical fresh acceptance 1 | Build 0, run 1, direct open Err without typed code | See fresh-secured-ledger1.sdn |
| Full-context diagnostic 2 | Build 0, run 1, SQLCIPHER4_MISSING_SECRET | f9f6a825f5a95a3a16c88f07c00974fbcea2420aca43747c047b3afefb12d5f6 |
| Minimal resolver control 3 | Build 0, run 0, exact and adjacent reference byte assertions | 0d90b03872565373cf2a9ddd4d2403eaf894b9dcea7310ab2129878137dd222a |

Diagnostic 2 runs the original fresh encrypted multi-page fixture with only
safe error-code reporting added. The direct environment presence check and
file geometry passed. The independent oracle and unchanged encrypted inputs/
metadata checks passed; page decoding and Messenger callbacks were unreached.
Diagnostic 3 deliberately excludes the Messenger/page-codec/KDF graph and
checks real SecretRef parse/resolve against synthetic ASCII environment values.
Both namespace slash and adjacent dash/dot folding passed with actual resolved
byte comparisons. This cannot establish full-context resolver behavior or KDF
Result ownership. No secret values were logged.

Logs and binaries remain in the diagnostic worktree at `D:/dev/simple-devhub-secured-db-p2-20261027/build/devhub-completion/`:
`fresh-secured-diagnostic2-{build,run}.log`, `fresh-secured-diagnostic2.exe`,
`key-resolution-probe3-{build,run}.log`, and `key-resolution-probe3.exe`.
The exhausted three-attempt count is preserved. No further diagnostic build or
unchanged test retry was started. The canonical bug remains OPEN P1 and TODO
377 remains blocked; the required next boundary comparison is in its bug record.
