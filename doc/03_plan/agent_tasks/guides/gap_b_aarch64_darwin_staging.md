# Guide B4 — aarch64-darwin hosted lane: stage the binary on a darwin host

Owner: one sonnet-class agent ON A MACOS AARCH64 HOST. Follow literally.

## Measured state (2026-09-05, macOS aarch64 host)

`test/03_system/plan_acceptance/aarch64_darwin_contract_snippet_spec.spl`
is 3/4: the sibling `test/03_system/os/qemu/sys_qemu_aarch64_darwin_fs_exec_spec.spl`
reports `CLASSIFIED: missing-media:build/os/darwin-aarch64/simpleos_aarch64_darwin_fs_exec`
and `outcome=ERROR`. `build/os/darwin-aarch64/` exists and is EMPTY.

## What to produce

Both paths named by `src/os/qemu_systest_contract.spl`
(`aarch64_darwin_binary_path()` / `aarch64_darwin_app_path()`):

- `build/os/darwin-aarch64/simpleos_aarch64_darwin_fs_exec` — the hosted
  fs-exec binary, built per
  `doc/03_plan/os/multiarch_qemu_systest/aarch64_darwin_contract_snippet.md`
  § build (the catalog entry `aarch64-apple-darwin` in
  `src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl` names
  `output` and `disk_image_output`; use the build command the plan gives for
  that entry — do not invent one).
- `build/os/darwin-aarch64/hello_world.smf` — the app it executes.

Then run the sibling directly and read its own line:

```
src/compiler_rust/target/debug/simple run test/03_system/os/qemu/sys_qemu_aarch64_darwin_fs_exec_spec.spl
```

It must print `CLASSIFIED: pass` and `outcome=OK`. If it prints a marker
name instead, that marker was not emitted by the binary — fix the binary,
never the marker list (the plan-acceptance spec pins the five `HOSTED_*`
markers and forbids the bare-metal ones).

## Acceptance

```
SIMPLE_BINARY=$PWD/src/compiler_rust/target/debug/simple \
  src/compiler_rust/target/debug/simple run test/03_system/plan_acceptance/aarch64_darwin_contract_snippet_spec.spl
```

→ `4 examples, 0 failures`, and its `[aarch64-darwin-sibling]` lines show
`outcome=OK`. No `E1034`.

On a LINUX host the same spec must instead show the sibling's
`MISSING BINARY (expected RED on Linux)` line and `outcome=ERROR` — that
branch is already what the spec asserts there; do not "fix" it.

Tick the four boxes at `doc/03_plan/os/multiarch_qemu_systest/aarch64_darwin_contract_snippet.md:236-239`
ONLY with `— verified <command> → 4 examples, 0 failures on <host os/arch>, <date>`.
