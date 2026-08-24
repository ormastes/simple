# `fn main(args: [text])` is unsupported and silently reads uninitialised memory (2026-08-24)

- Status: OPEN (P1 for the silent-garbage half) — call sites migrated, root cause NOT fixed
- Measured in `/mnt/data/worktrees/goal-lane-d-simpleos-fs`
- Blocked: `scripts/os/mkfs-dbfs.shs` and `scripts/os/mkfs-nvfs.shs`, i.e. the
  ability to format SimpleOS's own filesystems at all

## Symptom

`src/os/port/mkfs_dbfs.spl` and `src/os/port/mkfs_nvfs.spl` both declared
`fn main(args: [text])`. Running either through its wrapper:

```
$ sh scripts/os/mkfs-dbfs.shs build/os/simpleos_dbfs_root.img 65536
error: semantic: function expects argument for parameter 'args', but none was provided
```
rc=1.

## The dangerous half

Reduced to a two-line fixture:

```
fn main(args: [text]):
    print "n={args.len()}"
```

| invocation | result |
|---|---|
| `run m1.spl -- a b` | semantic error, rc≠0 |
| `run m1.spl a b` | semantic error, rc≠0 |
| `run m1.spl` | **rc=0, prints `n=8246223157400007265`** |

The no-argument case does not fail. It runs, and `args.len()` returns
uninitialised memory. A tool written against this signature will not crash — it
will branch on garbage. That is worse than the hard error and is why this is
filed P1 rather than as a missing feature.

## What was changed

Both mkfs entry points now read argv explicitly via
`std.nogc_sync_mut.io_runtime.get_args()`, which works correctly under the
current toolchain (it returns `[script_path, "--", ...user args]`, so a small
`_user_args()` helper drops the script path and the `--` separator). Each
carries a comment pointing here.

Verified after the change:
```
$ sh scripts/os/mkfs-dbfs.shs build/os/simpleos_dbfs_root.img 65536
mkfs.dbfs: wrote build/os/simpleos_dbfs_root.img (65536 sectors)
```
rc=0, 33554432-byte image produced.

## Not migrated

`/usr/bin/grep -rln 'fn main(args' src/` reports **11** files. Only the two mkfs
tools were migrated here, because only those were on this lane's critical path.
The other nine are still exposed to the silent-garbage behaviour above and
should be swept once the underlying signature is either implemented or rejected
at compile time.

## Fix order

1. Make `fn main(args: [text])` either work or be a hard compile error. It must
   never be a silent read of uninitialised memory.
2. Sweep the remaining 9 declarations.
3. Drop the `_user_args()` helpers if (1) implements the signature.

---

## Sharpened characterisation + full sweep (Lane H, 2026-08-24)

Binary under test: `bin/release/x86_64-unknown-linux-gnu/simple`, 60650360
bytes, mtime 2026-08-23 04:47:05 UTC (the Rust seed).

Three minimal reproducers, verbatim output:

```
$ cat a.spl
fn main(args: [text]):
    print "typed n={args.len()}"
$ simple run a.spl                  # rc=0
typed n=8246223157400007265
$ simple run a.spl x y
Segmentation fault (core dumped)    # rc=139

$ cat b.spl
fn main(args):
    print "untyped n={args.len()}"
$ simple run b.spl                  # rc=0
untyped n=-1
$ simple run b.spl x y              # rc=0
untyped n=-1

$ cat c.spl
fn main():
    print "noargs ok"
$ simple run c.spl x y              # rc=0
noargs ok
```

Two corrections to the original write-up:

1. **With argv the typed form does not "fail semantic analysis" — it SEGVs**
   (rc=139, core dumped). That is strictly worse than a diagnostic.
2. **The garbage length is not uninitialised noise — it is deterministic type
   confusion.** `8246223157400007265` == `0x72707845736d7261` == the ASCII
   bytes `armsExpr` (little-endian), i.e. a fragment of an interned compiler
   identifier string. It reproduced byte-for-byte across 3 consecutive runs, so
   ASLR is not involved: a non-array heap value is being read as the array
   header. Anything indexing with that length is an out-of-bounds read.

The **untyped** form `fn main(args)` is a *different* defect: `args` binds to
nil, `args.len()` is `-1` with and without argv. Not memory-unsafe, but it
means every `if args.len() > N` dispatch in the three `package/main.spl` tools
was dead — they always fell through to `show_help()`.

### Sweep completed

Census with `/usr/bin/grep -rn '^\s*fn main(\s*[a-z_]' --include=*.spl src/`
(after the mkfs migration) found **5** live offenders, all now migrated to
`get_args()`:

| file | old form |
|---|---|
| `src/lib/nogc_sync_mut/package/main.spl` | `fn main(args):` |
| `src/lib/nogc_async_mut/package/main.spl` | `fn main(args):` |
| `src/lib/gc_async_mut/package/main.spl` | `fn main(args):` |
| `src/os/port/e2e_verify.spl` | `fn main(args: [text]):` |
| `src/os/tools/simplebox/simplebox_main.spl` | `fn main(argv: [text]) -> i32:` |

Deliberately **not** migrated:
- `src/os/runtime/baremetal/runtime_minimal.spl:67` `fn main(argc: i32, argv: u64) -> i32:`
  — a C-ABI baremetal entry, a different contract.
- `src/compiler_rust/lib/std/src/tooling/html_utils.spl:361` `fn main(content: text) -> text:`
  — a module-local helper that happens to be named `main`, not an entrypoint.

`simplebox_main.spl` is busybox-style: `argv[0]` selects the applet
(`simplebox_requested_applet` reads it), so it passes the whole `get_args()`
vector through unmodified rather than using the `_user_args()` helper.

Ratchet: `test/01_unit/language/entrypoint/main_args_parameter_unsound_spec.spl`
walks the entrypoint directories and fails on any `fn main(<param>)`. Pre-fix it
reported `Results: 6 total, 5 passed, 1 failed` naming all 5 offenders; post-fix
`Results: 6 total, 6 passed, 0 failed`. It carries 5 detector self-checks so an
empty or broken scan cannot read as a pass.

### Unmasked pre-existing defect (separate, not fixed here)

With the untyped form the three `package/main.spl` dispatchers never executed —
`args.len()` was `-1`, so every command fell to `show_help()`. Now that argv is
real, `simple run src/lib/nogc_sync_mut/package/main.spl -- list` fails with
`error: semantic: variable 'PackageList' not found`: `main.spl` never imports
its sibling classes (`PackageBuild`/`PackageInstall`/... in `build.spl`,
`install.spl`, ...), and those files carry no `export` line either. The module
has therefore never worked as a CLI. This is a pre-existing rot that the nil
binding was hiding; it is now a loud failure rather than a silent help screen,
which is the correct direction. Fixing the package module's exports is a
separate change.

### Compiler-side fix: located, NOT made (routed — `src/compiler/**` is contended)

**No site in either tree inspects `main`'s declared parameter count before
calling it.** Every caller hardcodes an empty argument list, which is exactly
why the parameter slot is left holding a stale heap value.

Rust seed — `main` invocation sites, all zero-arg:
- `src/compiler_rust/compiler/src/interpreter_eval.rs:1985` — `exec_function(&main_func, &[], ...)`, with the literal comment `// No arguments`. **Primary defect site.**
- `src/compiler_rust/compiler/src/interpreter_eval.rs:656` — `entry_main` capture feeding the above.
- `src/compiler_rust/driver/src/exec_core.rs:786` — `jit.call_i64_void("main")`.
- `src/compiler_rust/driver/src/exec_core.rs:1311` — `em.execute("main", &[])`.
- `src/compiler_rust/driver/src/exec_core.rs:915` — `run_wasm_file(..., "main", &[])`.
- `src/compiler_rust/driver/src/interpreter.rs:549` — second JIT entry.

Self-hosted — `main` invocation sites, all zero-arg:
- `src/compiler/10.frontend/core/interpreter/eval_decls.spl:269-272` — `eval_function_call(main_decl, empty_args, [])` with `var empty_args: [i64] = []`. **Primary defect site.**
- `src/compiler/70.backend/backend/interpreter.spl:188-189`, `src/compiler/80.driver/driver_pipeline_execution.spl:47`,
  `src/compiler/70.backend/backend/jit_interpreter.spl:316-321`, `src/compiler/70.backend/codegen.spl:706`,
  `src/compiler/99.loader/loader/module_loader.spl:611`, `src/compiler/99.loader/module_loader_compat.spl:556`,
  `src/compiler/95.interp/execution/mod.spl:81`.

**argv is already available at every one of those sites** — it is published
before execution by `rt_set_args_vec` (`src/compiler_rust/driver/src/exec_core.rs:802,816,987`
and `src/compiler_rust/driver/src/cli/basic.rs:483`; store at
`src/compiler_rust/runtime/src/value/args.rs:204`, readers `rt_get_args`
`args.rs:248` and `rt_cli_get_args` `cli_sffi.rs:58`). The self-hosted
interpreter already declares the reader at
`src/compiler/10.frontend/core/interpreter/cli_eval.spl:11`
(`extern fn rt_cli_get_args() -> [text]`), and codegen already maps
`get_args`/`sys_get_args` -> `rt_get_args` at
`src/compiler/70.backend/backend/llvm_lib_translate_expr.spl:609`.

So option (a) — actually wiring argv — is a small change at the two primary
sites, not a new feature. Option (b) — rejecting the form — belongs where
`main` is already special-cased by name:
`src/compiler/20.hir/hir_lowering/_Items/lowering_helpers.spl:487,522` and
`declaration_lowering.spl:439-446`.

Neither was made here: `src/compiler/**` is under active contention by four
Stage-3 lanes, so this is reported for routing. Whichever lands, the ratchet
spec above should be kept — it costs nothing and pins the sweep.
