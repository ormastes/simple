# Native generated-source authority evidence

STATUS: FAIL — overall Phase 4 and five-host linker qualification remain open.

The source repair stages generated native-test entries beneath the canonical
checkout `test` directory and asks only the compiler coordinator to refresh its
source authority. Coverage and explicit AOT use canonical default roots. The
refresh token is consumed before worker dispatch; duplicate and worker requests
reject, while ordinary inherited builds preserve their existing behavior.
The runner does not clear its own authority environment.

Intent `b83b2acb980` preceded source `44d01e5fbcb`. Five new unit scenarios test
real staging, exact transformed bytes, uniqueness, invalid input, cleanup
ownership/retry and coordinator/argv behavior. One integration scenario creates
a real Git fixture and uses canonical cold/warm acquisition to test source
creation/deletion and older snapshot immutability. Existing LLVM/Cranelift
integration scenarios now use real `_spec.spl` positive/failing fixtures, a
separate zero-example program, an app import, and eight parent-binding checks.
Source review identified and corrected a test import and execution recipes.

Compilation requests the existing owned process route. An explicit unreaped
completion retains source, image and cache. Providers without a completion
receipt retain their existing synchronous contract; this is not proof of
universal descendant cleanup. Platform process and resource gates remain open.

All authored scenarios are UNRUN. No admitted full CLI/test runner has executed
this change; compiler/lib/MCP checks, core/native smoke, coverage, doctest/manual
generation and performance checks remain UNRUN. The separately owned full-CLI
attempt's terminal failure is recorded in the preceding recovery report. No
other owner's process/cache was changed, no bootstrap was restarted, and no
Rust-seed fallback was used. Source repair and structural checks cannot qualify
this feature for release or establish that all runtime blockers are resolved.

At the subsequent process revalidation, test-runner owner 37596 and collector
22612 were no longer live. The attempt-specific
`C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/phase34-post-link4/cranelift/phase4-test-runner/artifact/result.json`
records `exit_code: 139`, `compile_exit: 139`, `artifact_sha256: null`, and
`admitted: false`. This is a terminal failed attempt, not a verified wait or a
usable test runtime. The exit code alone does not identify its root cause.

Scoped structural checks against `4e18d0fd7f9102b5748e7e4821692c00eea5a097`
passed whitespace, direct-env runtime guards (working/staged) and numbered
artifact classification (five classified paths, zero numbered artifacts).
The prior zero-executable-spec audit for `doc/06_spec` remains applicable: this
change adds only Markdown there. Test-tree delta reports 3152 inherited
offenders and zero introduced. Its recorded list is
`C:/dev/simple/.git/item4-native-source-authority-preexisting-offenders.txt`,
SHA256 `2fb68a47bab7953e058a449562ecba2df9f135b8d2e2d99c3e14f373b1c1d719`.
This preserves the existing red-tree debt rather than claiming it is repaired.
