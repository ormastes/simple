# Pure-Simple SPipe Docgen Crashes on Vector-Font Spec

Status: open

The pure-Simple executable at
`build/bootstrap/full/x86_64-unknown-linux-gnu/simple` passes
`-c 'print(1+1)'` but exits by signal 11 when running:

```text
spipe-docgen test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl --output doc/06_spec --no-index
```

The newer stage3 candidate timed out on the same docgen lane, and both
candidates crash or no-op on the detached bitmap baseline probe. Canonical
`bin/simple` currently identifies itself as the forbidden Rust bootstrap seed.
Reproduce in an isolated worktree, fix the pure-Simple parser/compiler/docgen
owner, deploy a self-hosted binary, then run each blocked font command once.

## Re-triage 2026-08-17 (m9a_tests lane) — likely duplicate

Same mechanism as
`doc/08_tracking/bug/pure_simple_full_cli_process_run_inherit_spipe_docgen_crash_2026-07-18.md`:
the pure-Simple binary dying while delegating **spipe-docgen**, with a
different spec file as the subject. See that docs 2026-08-17 section for the
shared-cause argument; the two should be merged or cross-linked.

Scoping correction: `test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl`
is a plain spec with **no shell-out** (`grep -n "bin/\|release\|spipe-docgen"`
-> zero hits). Running the spec is not a reproduction; running spipe-docgen
over it is.

**Not reproduced from this lane** — the deployed `bin/simple` is the Rust
bootstrap seed, not a pure-Simple binary, so it cannot exercise the failing
path.
