# Native entry closure requires unavailable `rt_env_vars`

Date: 2026-09-09  
Status: open; blocks compiled Slang owner-fixture qualification.

## Reproducer

```text
simple native-build --backend=cranelift \
  --source test/fixtures/slang_paged_kv_provider --source src/lib \
  --entry-closure \
  --entry test/fixtures/slang_paged_kv_provider/owner_smoke.spl \
  --output /tmp/slang-owner-smoke-native
```

The fixture uses only the direct `rt_cli_get_args` intrinsic plus Slang modules,
but entry-closure compilation ends with:

```text
error: semantic: unknown extern function: rt_env_vars
```

## Required acceptance

- Report the exact dependency path that admits `rt_env_vars` into the closure.
- Either link its canonical runtime implementation or exclude the unrelated
  environment module from the closure.
- Build and run the real Slang owner fixture without adding a fake extern or
  broadening its runtime authority.

## 2026-09-12 extension: broader than `--entry-closure`, and not fixture-specific

Host: Windows 11, `bin/simple.exe` (Rust seed, 2026-09-02). Measured while
trying to native-build the TRACE32 CLI (`src/app/t32_cli` ->
`examples/10_tooling/trace32_tools/t32_cli`). Exit status read into a variable
on the next line, never through a pipe.

| probe | flags | rc | first error |
|---|---|---|---|
| t32 cli | `--runtime-bundle core-c-bootstrap --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/t32_cli/mod.spl` | 1 | `error: semantic: unknown extern function: rt_env_vars` |
| t32 cli, narrowed sources | same without `--source src/compiler` | 1 | identical |
| t32 cli, **no** `--entry-closure` | `--source src/app --source src/lib --entry src/app/t32_cli/mod.spl` | 1 | identical |
| **hello world** (`fn main(): print("ok")`, no imports) | `--source src/app --source src/lib --entry-closure` | 1 | identical |

Two corrections to the framing above:

- `--entry-closure` is **not** the trigger; dropping it changes nothing.
- It is not specific to the Slang fixture or to any user source. A two-line
  hello world with no imports fails identically, so any `native-build` on this
  host that includes `src/lib` in its sources is blocked.

Producer located: the message is `CompileError::semantic_with_context` from
`unknown_function()` at
`src/compiler_rust/compiler/src/interpreter_extern/common/error_utils.rs:23`,
i.e. the **interpreter** extern dispatch running inside the native-build worker
(`native-build worker exited with code 1. interpreter: bin/simple.exe`). Note
that `rt_env_vars` IS registered in three places the record's readers usually
check first — `runtime_symbols.rs:817`,
`codegen/runtime_sffi.rs:2001` (`RuntimeFuncSpec::new("rt_env_vars", &[], &[I64])`,
aliased to `rt_env_all`), and `interpreter_extern/mod.rs:1328`
(`insert_simple!("rt_env_vars", system::rt_env_all)`). So the gap is not a
missing registration but a sub-dispatcher that is reached without it; the
declaration the closure admits is
`src/lib/nogc_sync_mut/env/types.spl:15`, `extern fn rt_env_vars() -> [(text, text)]?`
(re-exported at `env/__init__.spl:50`, also declared at
`src/lib/nogc_sync_mut/io/env_ops.spl:8`, and imported without its own `extern`
declaration by `src/lib/nogc_async_mut/env/types.spl:8`).

Consequence for consumers: `t32 cli` cannot be made native on this host until
this is resolved. It is not blocked by anything in the TRACE32 sources — a
`bin/simple.exe run src/app/t32_cli/mod.spl --help` completes at rc=0 with
**zero** `[CODEGEN BODY]` / `[CODEGEN-STUB-FALLBACK]` markers, and marker
emission is eager (an uncalled function containing a bad bare reference still
emits one, verified), so the absence is evidence, not a gap in coverage.
