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
Status: open (workaround in place)
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
