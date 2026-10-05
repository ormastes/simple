# Shared macOS `bin/simple` predates `@when` stripping: nothing that imports `app.io` runs at HEAD

- **Filed:** 2026-10-04
- **Area:** seed deployment (macOS arm64)
- **Status:** OPEN — needs a seed redeploy; not a source defect

## Symptom

`bin/simple` on the macOS host resolves to
`src/compiler_rust/target/bootstrap.generations/f2b3edd25068…/simple` (built
2026-09-27). Every showcase entry fails before running:

```
error: compile failed: parse: in src/lib/nogc_sync_mut/io/windows_redirected_process.spl:
Unexpected token: expected Fn, found Colon
```

`windows_redirected_process.spl` (and six sibling `io/` files) use the
top-level `@when(os="windows"): … @else: … @end` block form added 2026-10-02.
The seed learned to strip those blocks for `simple run` in
`faa15917adc` (2026-10-03, `compiler/src/pipeline/cfg_strip.rs`), after the
deployed seed was built. A hello-world without imports still runs (0.08 s,
20 MB RSS).

## Evidence

- Paths in the error are the caller's worktree, so source resolution is
  per-worktree as expected; only the binary is stale.
- A seed built from `origin/main` 90c6e6ed27b (`cargo build --release --bin
  simple`) runs the same entries.

## Fix

Redeploy the macOS seed from current `origin/main` through the sanctioned
bootstrap path (`scripts/bootstrap/bootstrap-from-scratch.sh`), not by copying a
hand-built binary over `bin/`.
