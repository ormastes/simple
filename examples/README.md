# examples/ — retired as a showcase corpus

**The Simple examples corpus now lives at https://github.com/ormastes/simply**
(`examples/`), rendered at https://ormastes.github.io/simply/. Add new examples
there, not here.

## What is still in this directory, and why

This tree was **not** deleted wholesale. A reference census over the simple repo
found **732 non-doc files** (364 under `test/`, 182 under `scripts/`, 132 under
`src/`, plus `.github/`, `.spipe/`, `config/`, `tools/`) that build, test, or
execute paths under `examples/**`. Those paths are product and test
infrastructure that happens to live under an `examples/` name:

- `examples/09_embedded/` — SimpleOS boot/arch sources (`crt0.S`, baremetal
  stubs, per-arch entry `.spl`) consumed by `scripts/os/`, `scripts/check/`,
  `scripts/fpga/`, and the `test/03_system/feature/baremetal` lanes.
- `examples/05_stdlib/spipe/` — the SPipe toolchain source mirror.
- `examples/10_tooling/`, `examples/06_io/`, `examples/12_business/` — fixtures
  and demo targets referenced by check scripts and system tests.

Retiring the rest requires **moving that code out of `examples/` first** (into
`src/`, `test/fixture/`, or a tooling tree) and updating its referrers. That is a
separate, larger task; it is not a deletion.

## What was deleted

118 genuinely unreferenced showcase files (categories 01, 03, 04, 06_io, 07_ml,
08_gpu, 11_advanced, 99_scratch_debug, plus the `simple_cuda_example` submodule
gitlink and its `.gitmodules` stanza). Every one of them is preserved in the
simply repo, verified byte-identical before removal.
