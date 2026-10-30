# Seed interpreter: an `if` expression makes a frame re-read a stale module global

- **Filed:** 2026-10-31
- **Status:** OPEN
- **Lane:** Windows caret triage, Rust seed `simple test` / `simple run` (interpreter path)
- **Keeps RED:** `test/01_unit/app/llm_caret/main_spec.spl`, "should resume a saved provider model transcript and provider session" (`expected dummy to equal claude_cli`)

## Minimal repro

```
var G = "old"

fn f(c: bool) -> text:
    G = "new"
    val m = if c:
        "a"
    else:
        "b"
    G

print "returned=" + f(true) + " after=" + G
```

`seed run` prints `returned=old after=new`; correct is `returned=new after=new`.

Measured variants inside one function, after `G = <new>`:

| what follows the write | read of `G` |
|---|---|
| nothing | new |
| `if` statement assigning in both arms | new |
| plain call `val k = eff(G)` | new |
| `val m = if c: ... else: ...` | **old** |
| `H = if c: ... else: ...` | **old** |

## Product impact

`apply_resumed_session` (`src/app/llm_caret/main.spl:1187-1201`) writes
`RT_PROVIDER`, then assigns `RT_MODEL` from an `if` expression, then reads
`RT_PROVIDER`. It returns and persists the previous provider under the seed
(`_on_persist` afterwards also saved `dummy`). The product code and the spec are
correct; no reorder was applied, because that would hide this defect from every
other function with the same shape.

## Suspected site (not confirmed, seed not edited or rebuilt)

`src/compiler_rust/compiler/src/interpreter/block_exec.rs:242`:
`copy_back_block_writes` calls `refresh_live_bound_globals(env)`, reached from the
if-expression `BlockClosure` path at
`src/compiler_rust/compiler/src/interpreter/expr/control.rs:173-189`. A frame's
global write stays in its overlay until the frame returns
(`interpreter/expr/literals.rs:320-332`), so a refresh from the owner store would
overwrite the unpublished value. That matches the table: only value-position `if`
goes through this path.

## Unblock

Fix the seed so the refresh keeps overlay entries this frame wrote, rebuild the
seed, re-run `main_spec`. Not checked: whether the pure-Simple compiler or native
codegen share this defect (neither is runnable on this host).
