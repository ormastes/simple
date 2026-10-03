# Parser source traces must not count as admission diagnostics

Windows08e Phase3 LLVM inventory task143 exceeded its task-local RSS cap
(exit88). Its log included `[parser-expr] ... text=SCV-E-ADMISSION: ...` while
parsing CLI source. A substring classifier mistook that quoted source text
for a global admission failure and blocked the remaining module inventory.

The same substring match existed in bootstrap-scv-prime.shs. Its warm probe
now selects only a diagnostic beginning with `SCV-E-ADMISSION:` or
`error: SCV-E-ADMISSION:` followed by whitespace/end-of-line. Detection and
reported diagnostic share one selector. Unreadable evidence fails closed.
The existing warm timeout/crash policy is unchanged; this patch does not
turn an RSS-cap failure into a successful build or change resource limits.

Regression fixtures cover parser traces, quoted literals, ordinary mentions,
near-match codes, real direct/prefixed diagnostics, CRLF, mixed trace/error
logs and missing evidence. Execute
scripts/bootstrap/tests/scv-admission-diagnostic-test.shs and the existing
bootstrap-scv-prime.shs --selftest. Neither test compiles a native compiler.

Validation: classifier fixtures and mixed/CRLF/missing-log checks PASS;
all13existing SCV-prime self-checks PASS. Native bootstrap was not rerun.

Windows diagnostic attempt3 is independently owned. Linux prepared launcher
contains a similar classifier; coordinate its frozen ownership before edits.
