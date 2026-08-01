# `rt_process_spawn_async` always returns pid=-1 under JIT (`bin/simple run`)

**Status:** FIXED — one-line addition to `process_c_runtime_arg_indices` in
`src/compiler_rust/compiler/src/codegen/instr/calls.rs`
**Found:** 2026-07-31
**Fixed:** 2026-07-31
**Engine:** JIT (Cranelift) only. Interpreter and `-c` (interpreter path) are unaffected.

## Fix applied

```rust
"rt_process_run"
| "rt_process_run_inherit"
| "rt_process_spawn"
| "rt_process_spawn_async"          // <-- added
| "rt_process_spawn_guarded"
| "rt_process_execute"
| "rt_process_run_timeout"
| "rt_process_run_bounded" => Some((&[0], &[1])),
```

Confirmed before applying: `rt_process_spawn_async` (`env_process.rs:706`) has
the byte-identical `(cmd_ptr: *const u8, cmd_len: u64, args: RuntimeValue) -> i64`
signature as `rt_process_spawn` (`env_process.rs:654`), and both are registered
with the identical 3×I64 -> I64 `RuntimeFuncSpec` in
`codegen/runtime_sffi.rs:1333` (`rt_process_spawn_async`) vs `:1322`
(`rt_process_spawn`), so `(&[0], &[1])` is the correct expansion mapping — same
as its sibling.

## Family audit (requested alongside the fix)

Every `rt_process_*` extern in `src/compiler_rust/runtime/src/value/sffi/env_process.rs`
was cross-checked against `process_c_runtime_arg_indices`:

| Function | `(cmd_ptr, cmd_len, ...)` shape? | In the table? |
|---|---|---|
| `rt_process_run` | yes | yes |
| `rt_process_run_inherit` | yes | yes |
| `rt_process_spawn` | yes | yes |
| `rt_process_spawn_async` | yes | **fixed, now yes** |
| `rt_process_spawn_guarded` | yes | yes |
| `rt_process_execute` | yes | yes |
| `rt_process_run_timeout` | yes | yes |
| `rt_process_run_bounded` | yes | yes |
| `rt_process_spawn_inherit` | no args | n/a (correctly absent) |
| `rt_process_is_running` | no text arg | n/a (correctly absent) |
| `rt_process_exists` | no text arg | n/a (correctly absent) |
| `rt_process_wait` | no text arg | n/a (correctly absent) |
| `rt_process_kill` | no text arg | n/a (correctly absent) |
| `rt_process_run_with_limits` | yes (`cmd_ptr, cmd_len, args, timeout_ms, memory_bytes, cpu_seconds, max_fds, max_procs`) | **no — but not a live gap for this bug family** |

`rt_process_run_with_limits` is **not** reachable through
`process_c_runtime_arg_indices` at all today because it has no call-site
lowering anywhere in the compiler frontend (only `elf_utils.rs`'s
function-pointer table and its `RuntimeFuncSpec` in `runtime_sffi.rs:1337`
reference it, and neither is a Simple-level call path). Separately, its
`RuntimeFuncSpec` already only declares 5 `I64` args
(`codegen/runtime_sffi.rs:1337`) against the real 8-parameter Rust signature —
a pre-existing, unrelated arg-count mismatch, not a missing ptr/len expansion.
Not touched here per the "no speculative entries" scope of this fix; filed as
a separate latent-dead-code observation, not a live JIT defect, since nothing
currently calls it.

## Verification (non-vacuous, fixed vs reverted, same build recipe)

Built `cargo build --profile bootstrap -p simple-driver --features llvm`
(154 MB binary, LLVM present) twice in a fresh `git worktree --detach` at
origin tip `bb68496f95bd7a0819ca17ab9204b001fb666b36`: once with the fix
applied, once with it reverted (`git checkout --`), same probe both times:

```simple
extern fn rt_process_spawn_async(cmd: text, args: [text]) -> i64
extern fn rt_process_spawn(cmd: text, args: [text]) -> i64
extern fn rt_process_spawn_guarded(cmd: text, args: [text]) -> i64
extern fn rt_process_run(cmd: text, args: [text]) -> (text, text, i64)

fn main():
    val pid_async = rt_process_spawn_async("/bin/echo", ["hello-async"])
    print("ASYNC_PID=" + pid_async.to_text())
    val pid_spawn = rt_process_spawn("/bin/echo", ["hello-spawn"])
    print("SPAWN_PID=" + pid_spawn.to_text())
    val pid_guarded = rt_process_spawn_guarded("/bin/echo", ["hello-guarded"])
    print("GUARDED_PID=" + pid_guarded.to_text())
    val (stdout, stderr, exit_code) = rt_process_run("/bin/echo", ["hello-run"])
    print("RUN_STDOUT=" + stdout)
    print("RUN_EXIT=" + exit_code.to_text())
```

**Fixed binary**, `bin/simple run probe.spl` (JIT, default):
```
ASYNC_PID=2001643        # real pid, child ran ("hello-async" printed)
SPAWN_PID=2001647
GUARDED_PID=2001651
RUN_STDOUT=hello-run
RUN_EXIT=0
```

**Reverted binary** (`git checkout -- calls.rs`, rebuilt, same probe),
`bin/simple run probe.spl`:
```
ASYNC_PID=-1              # bug reproduced
SPAWN_PID=2198390          # sibling controls still correct
GUARDED_PID=2198391
RUN_STDOUT=hello-run
RUN_EXIT=0
```

Fix re-applied after the revert test and landed. This proves the change is
both necessary (revert reproduces `-1`) and sufficient (fix produces a real
pid), and that the three sibling regression controls
(`rt_process_spawn`, `rt_process_spawn_guarded`, `rt_process_run`) are
unaffected in both states.

## Symptom

`rt_process_spawn_async(cmd, args)` called from a `.spl` program run via
`bin/simple run <file>` (the default JIT engine) always returns `pid=-1`, even
for a trivially valid spawn (`/bin/echo`). The same call under
`bin/simple -c '<code>'` (interpreter) or `SIMPLE_EXECUTION_MODE=interpret
bin/simple run <file>` returns a real pid and the child actually runs.

This is **not** a general "spawning is broken" defect. It is scoped narrowly:
sibling functions with an identical Rust signature
(`rt_process_spawn`, `rt_process_spawn_guarded`, `rt_process_run`,
`rt_env_get`) all work correctly under the same JIT engine, in the same probe
file, in the same process.

## Reproduction (proved, deployed binary `bin/release/x86_64-unknown-linux-gnu/simple`, built 2026-07-30 15:26, no rebuild)

```simple
extern fn rt_process_spawn_async(cmd: text, args: [text]) -> i64
fn main():
    val pid = rt_process_spawn_async("/bin/echo", ["hello-from-probe"])
    print("PID=" + pid.to_text())
```

| Invocation | Result |
|---|---|
| `bin/simple run probe.spl` (JIT, default) | `PID=-1` |
| `bin/simple -c '...'` (interpreter) | `PID=<real pid>`, child's stdout printed |
| `SIMPLE_EXECUTION_MODE=interpret bin/simple run probe.spl` | `PID=<real pid>`, child's stdout printed |
| `SIMPLE_EXECUTION_MODE=jit bin/simple run probe.spl` (explicit) | `PID=-1` |

Sibling calls in the same JIT run, same process, same file:

| Call | Under JIT `run` |
|---|---|
| `rt_env_get("HOME")` | works |
| `rt_process_spawn("/bin/echo", [...])` (sync spawn) | works, correct pid, child output printed |
| `rt_process_run("/bin/echo", [...])` (capture output) | works, correct exit code + captured stdout |
| `rt_process_spawn_guarded("/bin/echo", [...])` | works, correct pid, child output printed |
| `rt_process_spawn_async("/bin/echo", [...])` | **`-1`, no child, no output** |

## Root cause (proved by code read + differential test, not by rebuild)

`src/compiler_rust/compiler/src/codegen/instr/calls.rs`, function
`process_c_runtime_arg_indices` (~line 2550):

```rust
pub(crate) fn process_c_runtime_arg_indices(func_name: &str) -> Option<(&'static [usize], &'static [usize])> {
    match func_name {
        "rt_process_run"
        | "rt_process_run_inherit"
        | "rt_process_spawn"
        | "rt_process_spawn_guarded"
        | "rt_process_execute"
        | "rt_process_run_timeout"
        | "rt_process_run_bounded" => Some((&[0], &[1])),
        _ => None,
    }
}
```

This table tells the JIT codegen which extern-call argument indices are Simple
`text` values that must be expanded from a single boxed `RuntimeValue` into the
`(ptr: *const u8, len: u64)` pair the linked Rust runtime function actually
expects (see `expand_text_args`, same file, ~line 2568, and
`src/compiler_rust/runtime/src/value/sffi/env_process.rs`, where every one of
these functions is declared as
`extern "C" fn(cmd_ptr: *const u8, cmd_len: u64, args: RuntimeValue) -> i64`).

**`rt_process_spawn_async` is declared with the identical
`(cmd_ptr: *const u8, cmd_len: u64, args: RuntimeValue)` signature
(`env_process.rs:706`) and the identical 3-arg `I64,I64,I64` arity in
`runtime_sffi.rs:1333`, but it is missing from this match arm.**

Consequence under JIT: the `cmd: text` argument is passed as one raw boxed
value instead of being split into `(ptr, len)`. The call site then supplies
one fewer real argument than the runtime function's parameter list expects, so
the callee reads a garbage/misaligned `cmd_ptr` (the tagged string value's raw
bits, not a real byte pointer) and `cmd_len` (bits belonging to what should
have been the `args` array), while the true `args` value lands in an
undefined third slot. In `rt_process_spawn_async` (env_process.rs:706-747)
this either fails UTF-8 validation or fails at `command.spawn()`, both of
which return `-1` — with no panic and no diagnostic, matching the observed
silent behavior.

This is a leftover gap from the exact same bug family already swept and fixed
in `doc/08_tracking/bug/extern_text_cchar_abi_family_sweep_2026-07-29.md`
(2026-07-29): that sweep covered `rt_cuda_*`/`rt_profiler_record_call`
against `RUNTIME_FUNCS`, but the sibling `process_c_runtime_arg_indices` table
in the same file was not re-audited against all process-spawn variants, and
`rt_process_spawn_async` — added/kept in `runtime_sffi.rs` with the correct
3-arg spec — was never added to `process_c_runtime_arg_indices`.

## What was ruled out

- **Not** a general "process spawning is broken under JIT" defect — 4 sibling
  functions with the same signature shape work correctly under the same
  engine, same process, same probe file.
- **Not** a security/ambient-API runtime gate — `rt_process_spawn_async` and
  `rt_process_run` are both listed in `security.rs`'s `raw_ambient_api_patterns`
  (used for static lint scanning of raw ambient-capability calls only), but
  `rt_process_run` works fine under JIT and `rt_process_spawn` (not in that
  list at all) also works, so list membership there is uncorrelated with the
  failure.
- **Not** a symbol-resolution / linkage problem — `elf_utils.rs` and
  `runtime_sffi.rs` both map `rt_process_spawn_async` to the correct function
  pointer and correct arity; the JIT does not report an unresolved-symbol
  fallback message for it (which would have de-JITted the whole module and
  still produced a correct, if slow, result).
- **Not** a cwd/module-resolution difference between `run` and `-c` — the
  same probe file and same binary were used for both.
- **Not** binary-specific — the deployed
  `bin/release/x86_64-unknown-linux-gnu/simple` is the Rust bootstrap seed
  (it prints "this Rust-built Simple binary is a bootstrap seed only"), and
  this is the binary all four invocation modes above were run against; no
  fresh build was performed for this diagnosis.

## Original suggested fix (now applied — see "Fix applied" above)

Add `"rt_process_spawn_async"` to the `process_c_runtime_arg_indices` match
arm in `src/compiler_rust/compiler/src/codegen/instr/calls.rs`, mirroring its
siblings: `"rt_process_spawn_async" => Some((&[0], &[1]))`. No runtime or
`runtime_sffi.rs` change was needed — both already assumed the `(ptr, len)`
expansion happens at the call site. This prediction was confirmed by the
fixed-vs-reverted rebuild test above.

## Verification commands used (deployed binary, no rebuild)

```bash
SIMPLE_BIN=bin/release/x86_64-unknown-linux-gnu/simple
"$SIMPLE_BIN" run probe.spl                                  # PID=-1
"$SIMPLE_BIN" -c '...same call...'                            # PID=<real>
SIMPLE_EXECUTION_MODE=interpret "$SIMPLE_BIN" run probe.spl   # PID=<real>
SIMPLE_EXECUTION_MODE=jit "$SIMPLE_BIN" run probe.spl         # PID=-1
```
