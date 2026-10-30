# Windows Phase 2 runner environment snapshot ABI and process admission

Status: OPEN. The source adapter and standalone runner guard are provisional;
end-to-end native test execution remains blocked and is not a passing gate.

The Windows GNU Phase 2 producer built a standalone runner. Its native test
execution initially rejected an invalid environment assignment. Review of the
linked executable found that `rt_env_vars` returns array-backed runtime tuples,
while generated tuple destructuring read flat tuple fields. The environment
owner now explicitly reads the runtime tuples and constructs typed pairs.

A subsequent runner build passed process environment validation but failed
with `Windows process request allocation failed`. The first Hello SSpec
reported 0 passed and 1 failed. No eight-case runner success is claimed. The
Phase 2 compiler separately passed the canonical Stage 2 Hello gate (two
checks); that is not evidence that the test runner can execute the cases.

The standalone runner guard rejected an absent compiler and itself as compiler
with exit 2 in the earlier build. Its later source-entry correction and the
combined release-head integration are not independently executed. Windows
lexical path normalization does not prove same-file identity for hardlinks.

Local evidence: `C:/dev/simple-phase2-smux-runner-20261028/` contains
`canonical-hello-gate.log`, `hello-runner-envfix-1.log`, and build logs. The
compiler is the bootstrap executable with SHA256 beginning `13d73267`; it is
Phase 2 despite its `stage3` directory name. The temporary C inclusion used to
build the older producer is not a release change: newer runtime builds compile
that owner separately and would risk duplicate symbols.

Next: repair and exercise Windows process allocation and cleanup, run all eight
native Hello cases with real process execution and retained artifacts, verify
the integrated runner and environment snapshot semantics, and qualify an
actual GNU Phase 3 compiler before making a Phase 3 claim.
