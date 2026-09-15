# `native-build` is red tree-wide: `semantic: unknown extern function: rt_env_vars`

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-11, `work/bootstrap-codegen-1-2026-09-13`, base `origin/main f26970e9d93`
- Severity: **blocks every native measurement.** No `.spl` can be native-built on
  this tree with any deployed binary, so no native-codegen defect can be
  reproduced, and no native-codegen fix can be proven.

## Verdict, verbatim

```
SCV-E-SNAPSHOT: snapshot-inventory-unavailable
error: semantic: unknown extern function: rt_env_vars
error: native-build worker exited with code 1.  interpreter: <deployed binary>
```

## Reproduced on every shape tried

| driver | flags | result |
|---|---|---|
| `bin/simple` (deployed seed, sha256 `3d120a6f9ab5704b`) | `native-build --entry <f> --entry-closure --cache-dir <d> -o <o>` | `rt_env_vars`, rc=1 |
| same | `--backend llvm --mode dynload` | `rt_env_vars`, rc=1 |
| bootstrap seed `011f3177637b6feb` | `SIMPLE_BOOTSTRAP=1 --backend llvm --runtime-bundle core-c-bootstrap --entry-closure --mode one-binary` | `rt_env_vars`, rc=1 |

**The control fails too.** `scripts/check/cert/redeploy_gate/fixtures/hello_world.spl`
— the redeploy gate's own fixture, three lines, no imports — fails identically.
So this is not input-specific.

**Independently reproduced in another worktree.** The shared `/tmp` carries
`native-build-stderr-252595-1.log` from `/home/yoon/dev/simple-todofix-3` with
byte-identical symptoms at the same timestamp, so it is not this worktree's
setup either.

## Not the obvious cause

`rt_env_vars` IS registered in the deployed binaries' interpreter dispatch
(`interpreter_extern/mod.rs:1328`, `insert_simple!("rt_env_vars", system::rt_env_all)`)
and in `codegen/runtime_sffi.rs:2014`. Probed directly on both binaries with a
two-line program that declares `extern fn rt_env_vars() -> [(text, text)]?` and
calls it: both print `ok`. A second probe proved a re-exported extern
(`module A declares + exports`, `module B imports and calls`) also resolves.
So the failure is NOT a plain missing registration and NOT the simple
re-export hop.

Remaining suspects, in order, not yet discriminated:
1. the `$dupN` mangling for co-compiled duplicate definitions — the same build
   warns that `env_vars` has 2 definitions with differing signatures
   (`()->Optional([Tuple([text, text])])` vs `()->[Tuple([text, text])]`), and a
   mangled name would miss the dispatch table;
2. a family-restricted import path — the failure is preceded by
   `[gc-warning] Higher-layer module 'std.nogc_sync_mut.env.types' ... imported in
   restricted context (family: nogc_async_mut)`;
3. the `[use-warning] 'rt_env_cwd' is named in use std.io_runtime.{...} but
   module src/std/io_runtime.spl does not provide it` on the same module.

## Why it matters beyond this lane

`test/03_system/compiler/native_cross_module_class_field_layout_regression_spec.spl`
and every other spec that shells out to `native-build` cannot pass at this
commit. A green `bin/simple test` run is therefore NOT evidence about the native
lane today.
