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
