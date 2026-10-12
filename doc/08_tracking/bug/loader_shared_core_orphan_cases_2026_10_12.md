# Loader shared-core orphan test cases

Bug: `loader_shared_core_orphan_cases_2026_10_12`.
Canonical bug DB reconciliation is pending.

`test/01_unit/compiler/loader/loader_shared_core_spec.spl` begins with three
indented `it` cases without their enclosing `describe`. This invalid source
blocked the generated loader test binary before code generation.

The repair adds only `describe "Core language regression oracles":`.
All five cases, fifteen assertions, test setup, and suite execution are
preserved. No test is commented out or replaced with a placeholder.

Original source SHA-256:
`623ac0fae775cbc04351ec6906907447a32f6efe2e21255a0b8860f550694b72`.
Private corrected source SHA-256:
`997ad8f03c9185366834a72880e1415695a2ee9685ac612fbf4898fcae7271e5`.

Astra regenerated the actual 239-owner loader registry using the retained
generator. Only the corrected owner's generated output changed; the other
238 remained byte-identical. The subsequent native build passed this parser
boundary and exposed separate architecture/assembly and trace-framing
blockers. Registry source contains 1,315 textual cases; this count is not
runtime enumeration or test execution.

Evidence: `build/native_probe/loader239-llvm-d958-20261012-astra/registry-repair/`.
Terminal product evidence: `FINAL239_RESULT.md` in the parent directory.
The three-attempt native product criterion is exhausted with no executable;
this repair does not qualify a test binary or any passing runtime cases.

Remaining prevention: reject orphan cases during registry generation with
source location evidence, and verify the real loader binary after the
independent producer/configuration fixes. Generator prevention is unrun.
