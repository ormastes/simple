# silent_default lint was unreachable dead code at origin after a stale-snapshot clobber

**Status:** FIXED 2026-08-17 (wiring restored, ablation measured both arms).

## Summary

`e14a2ffb4df` ("three fail-open sites made fail-closed") was a stale-snapshot
clobber. Earlier lanes restored six of the seven silent_default files it removed
(`src/compiler/35.semantics/lint/silent_default.spl`,
`doc/07_guide/lint/silent_default_lint.md`,
`scripts/check/check-silent-default-baseline.shs`,
`scripts/check/silent_default_baseline.txt`, and BOTH specs). Because every file
was present again, the restoration LOOKED complete.

It was not. The clobber also deleted the rule's entire WIRING from three files it
merely MODIFIED, so no deleted-file census could see it:

| file | lost |
|---|---|
| `src/compiler/35.semantics/lint/__init__.spl` | `export silent_default.*` |
| `src/compiler/90.tools/lint/_LintMain/lint_checks.spl` | `use compiler.semantics.lint.silent_default.{check_silent_default}`; the `self.check_silent_default_spl(path, content)` dispatch line; the whole `me check_silent_default_spl` method |
| `src/compiler/90.tools/lint/_LintMain/config_and_model.spl` | the `"silent_default"` configurable-name entry; the `levels["silent_default"] = "warn"` escalation point; the `W-MC-DEF-001/002/003 -> "silent_default"` code-to-name mapping |

`check_silent_default` therefore had **zero callers**: the rule was complete,
documented, spec'd, baseline-gated — and never executed.

**Why the two existing specs did not catch it (they are not a discriminator).**
`test/01_unit/compiler/lint/silent_default_{detection,reproducer}_spec.spl` both
`use compiler.semantics.lint.silent_default.{...}` DIRECTLY, bypassing the
`__init__.spl` re-export and the `_LintMain` dispatch entirely. They pass in both
arms and prove only that the rule's own logic works, never that anything calls
it. Presence of a green spec is not evidence a feature is reachable.

## Ablation (real discriminator: `simple lint` on a fixture)

Binary: Rust seed `bin/release/x86_64-unknown-linux-gnu/simple`, size 59537240,
mtime 2026-08-17 12:58:51 UTC. Reverted arm = isolated `git worktree` pinned at
`origin/main`. Fixture:

```
fn probe(s: text) -> i64:
    val idx = s.index_of("(").unwrap_or(0)
    idx
```

Reverted arm (`V2_REVERTED_LINT_RC=0`), W-MC-DEF hit count `0`:

```
Lint passed: all files clean
```

Applied arm (`V2_APPLIED_LINT_RC=0`), W-MC-DEF hit count `1`:

```
sd_fixture.spl:2:0: warning[W-MC-DEF-001]: in-domain default `0` substituted for a failed `index_of` lookup; a caller cannot tell it from a real result
```

The rule fires only after the wiring is restored. `Lint passed: all files clean`
still appears in the applied arm because the level is `warn`, not `deny` — that
is the intended default and the escalation point is the single
`levels["silent_default"]` line.

## Lesson for clobber census

Two independent ways a file-granular census reports a false all-clear:
presence of a file does not mean its content is complete (this bug — 6 of 7
files back, feature still dead), and presence of a spec does not mean its fix is
present, nor that the spec exercises the path that was lost.
