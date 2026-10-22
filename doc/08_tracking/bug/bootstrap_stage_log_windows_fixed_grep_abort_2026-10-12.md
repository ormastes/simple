# Windows stage-log diagnostic matcher drops a real build failure

Status: classifier repaired and shell regressions passed; the bootstrap failure itself is separate.

Attempt10 terminated stage2 with exit1 and a 385-byte UTF-8 log. It contained `Build failed: failed to parse ...driver_hir_archive_journal_v1.spl at 145:83 during discovery: Unexpected token: expected expression, found Else`. The stage-log guard nevertheless returned exit1 and called it UNDIAGNOSABLE. Direct matching against the existing `build failed` diagnostic alternative succeeded.

The failing step was the SCV source-quotation exclusion: Git/MSYS GNU grep3.0 aborts with exit134 for `LC_ALL=C grep -i -v -F 'SCV-E-ADMISSION' LOG`. The classifier suppresses this command's stderr. Its downstream diagnostic matcher receives no lines, so the count becomes zero. This is not a missing diagnostic alternative or a compiler success.

The exclusion now uses `-E` in place of `-F`. The fixed ASCII token contains no ERE metacharacters, so this preserves case-insensitive substring exclusion, including quoted SCV text on legacy `error:` or `Build failed` lines. The anchored canonical SCV reason owner remains unchanged. Bare SCV codes and source quotations remain insufficient evidence.

Validation used Git Bash on Windows: all35 shell selftest fixtures passed, including the actual Windows discovery message as primary and sibling evidence, mixed-case UTF-8 diagnostic text, genuine canonical SCV reasons, bare codes, upper/lowercase source quotations, and a quoted SCV line followed by an independent real cause. Existing empty/missing/progress-only and enforced-resource receipt negative cases still fail closed. The preserved attempt10 log now returns classifier exit0 with its actual parser failure excerpt and retains the stage's exit1 in the verdict. Its source bytes and SHA256 were unchanged.

No compiler, native runtime, C, or Rust build was run for this repair. The parser grammar failure is owned by the next-source compiler fix, not this diagnostic guard.
