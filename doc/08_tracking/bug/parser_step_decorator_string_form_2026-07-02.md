# Parser: `@step "label"` decorator form fails — "expected Fn, found FString"

## Re-verified 2026-09-13 — STILL REPRODUCES (left open)

Verification engine: pinned copy of `src/compiler_rust/target/release/simple.exe`
(Simple Language v1.0.1-beta.1, 39,267,840 bytes, sha256 prefix `1b62a1a42755774fc087`,
built 2026-09-13 on this host). Windows 11 / Git Bash, default `run` lane
(seed JIT with interpreter fallback). This is the **Rust bootstrap seed**, not a
deployed pure-Simple self-hosted binary — the self-hosted lane remains unverified
on this host.

Ran a file using the decorated-string form the SPipe template advertises:

```spl
@step "Open the application"
fn open_app():
    print("ok")
```

Result, verbatim and identical to the 2026-07-02 report:

```
parse: Unexpected token: expected Fn, found FString([Literal("Open the application")])
```

Both resolutions the entry offers are still available and neither has been
taken: the parser does not accept `@step "label"`, and
`.claude/templates/spipe_template.spl` still advertises it. Left open rather
than fixed here because the parser half lives in `src/compiler_rust/**`,
which a concurrently running bootstrap forbids editing.

Date: 2026-07-02
Status: SUPERSEDED 2026-11-11 (lane compiler6) — template corrected + convention codified (MNT-003); parser change no longer the chosen resolution. See the 2026-11-11 addendum at the end of this file.
Severity: P3
Related: .claude/templates/spipe_template.spl, SPipe SSpec authoring

## Symptom

The SPipe template (`.claude/templates/spipe_template.spl`) shows the
decorator form on its own line before a function:

```simple
@step "Open the application"
fn open_app():
    ...
```

Parsing any spec that uses this form fails:

```
parse: Unexpected token: expected Fn, found FString([Literal("Open the application")])
```

Working specs in the tree all use the comment form `# @step: ...` instead.
Either the parser should accept the decorated-string form the template
advertises, or the template should be corrected to the comment form.

## Repro (verified 2026-07-02)

`bin/simple run` any spec containing `@step "x"` above a top-level `fn`,
e.g. the pre-fix version of
`test/03_system/check/gui_low_res_readability_spec.spl`.

## Workaround

Converted the spec's `@step "..."` lines to `# @step: ...`.

## Verdict addendum 2026-11-11 — lane compiler6 (SUPERSEDED)

Verified on the tracked fresh seed (`bin/simple.exe`, build 46fe8f6b6def,
seed-smoke): a spec using the decorated-string form still fails with
`Unexpected token: expected Fn, found FString([Literal("Open the application")])`
at line 2, column 7 — the parse behaviour is unchanged.

The record itself allowed two resolutions: "Either the parser should accept
the decorated-string form the template advertises, or the template should be
corrected to the comment form." The second branch has since been taken and
codified:

* `.claude/templates/spipe_template.spl` no longer advertises `@step "..."`.
  Its score-bearing structure block now mandates: "never a bare `@step "..."`
  decorator; use `# @step:` (MNT-003)".
* The SPipe authoring convention `.claude/skills/spipe.md` rule **MNT-003**
  scores any line starting with `@step ` at -10 mnt and prescribes
  `# @step: Label` instead.
* Both arrived via merge `9e7e7a526edb` (PR #7597, 2026-11-07), the sspec
  modernization lane.
* Working specs in the tree use the comment form; docgen binds `# @step:`
  comments (template header: "`# @step:` overrides the label").

With the template corrected and the convention enforced by the scorer, the
parser half of this record is no longer the chosen resolution: blessing a form
the style guide penalizes would contradict the owner's documented convention,
and landing it would need a Rust seed rebuild this lane is not granted.
SUPERSEDED, CLOSED.
