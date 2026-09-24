# Bug — `bin/simple check` broken tree-wide (seed semantic error + stale worker)

Date: 2026-09-24. Found during the rendering-showcases lane verification (all
six parallel lanes hit this independently).

## Symptom

`bin/simple check <file.spl>` fails for EVERY input in the current tree,
including pristine known-good files (`examples/01_getting_started/hello_native.spl`,
`src/lib/common/ui/wm_chrome_theme.spl`,
`examples/06_io/ui/wm_multiapp_taskbar_gui.spl`).

Observed errors (vary by file/lane):

- `error: semantic: class TraitSolver has no field named impl_arena` —
  `src/app/check/main.spl` does not compile under the current Rust seed
  binary.
- `error: semantic: missing importing module surface` / `unresolved name`
  for any `use app.*` import unless `SIMPLE_LIB=src` is set.
- The fast check worker (`bin/release/aarch64-apple-darwin/simple`, Jul 25)
  is stale and cannot load the check entry either (see related stale-toolchain
  issues; it also cannot parse stdlib sources newer than 2026-09-14).

## Workaround (used by the showcases lanes)

`SIMPLE_LIB=src SIMPLE_TIMEOUT_SECONDS=0 bin/simple run <file.spl>` performs
the full semantic pass plus execution and is the effective gate until this is
fixed. `bin/simple check --syntax-only` works but is parse-only.

## Expected

`bin/simple check <file>` compiles the check entry under the seed and returns
real per-file diagnostics; the deployed release worker is current enough to
parse current stdlib.

## Related

- Deployed toolchain staleness: `bin/simple` is a symlink to the Rust seed;
  `bin/release/aarch64-apple-darwin/simple` predates 2026-09-14 stdlib syntax.
