# `check-native-trailing-default-param.shs` red — three stacked causes, none of them the trailing-default lane

- **Filed:** 2026-08-17
- **Status:** OPEN — guard RED on every binary tried; blocks pushes for every lane
- **Supersedes the diagnosis (not the rows) of:**
  - `native_trailing_default_param_guard_red_at_origin_tip_2026-08-15.md` ("environmental")
  - `native_trailing_default_param_guard_static_method_receiver_undefined_2026-08-17.md` ("undefined variable Widget")
  Neither error is reachable today; the build dies earlier, in a different place, for a
  different reason, and on a different binary each time. Those rows are left untouched.

## The guard is not testing what its verdict says

`--source test/fixtures` is not the whole story: `native-build` shells out to
`src/app/cli/native_build_worker.spl`, run through the **pure-Simple compiler
driver interpreted by the seed**. So the guard transitively compiles and executes
`src/compiler/**`, `src/app/**` and `src/lib/**`. Any defect anywhere in that
surface FAILs the guard with `native-build failed to compile the fixture`,
attributing a whole-compiler outage to a 60-line fixture. The fixture itself was
never reached in any run below.

## Cause 1 — seed interpreter cannot dispatch ANY method on a `class` (2 of 3 binaries)

Verdict text: ``error: semantic: method `compile` not found on type `object`
(receiver value: CompilerDriver(...))``. Reproduced down to **8 lines**, no repo
imports, no `impl` block required:

```simple
class T:
    n: i64
    me inline() -> i64:
        self.n

fn main() -> i64:
    val t = T(n: 10)
    print("inline={t.inline()}\n")
    0
```

| binary | built | `SIMPLE_EXECUTION_MODE=interpreter` | jit / default |
|---|---|---|---|
| `/mnt/data/cargo-brk/release/simple` | 11:59 | **`method inline not found on type object`** | `inline=10` |
| `/mnt/data/cargo-vhdl/release/simple` | 12:36 | **`method inline not found on type object`** | `inline=10` |
| `bin/release/x86_64-unknown-linux-gnu/simple` | 12:58 | `inline=10` | `inline=10` |

Notes that pin it down:
- `struct S` + `impl S` is **fine**; only `class` is affected. The receiver's type
  name degrades to `object`, which is why the whole class method table is missed.
- It is the **interpreter only**. `native_build_main.spl` forces
  `SIMPLE_EXECUTION_MODE=interpret` for the worker when unset, so every
  `native-build` lands on the broken engine. Setting `jit` does not help: the
  compiler tree is large enough that the JIT falls back to the interpreter
  (`[INFO] JIT compilation failed, falling back to interpreter`) and lands in the
  same place.
- The 12:58 deployed seed is *smaller* (59,537,240 B) than both lane seeds
  (59,601,704 / 59,602,688 B) — a different build config, not merely newer. Which
  side is origin/main tip is **unresolved** and must be settled before anyone
  claims this is fixed.

Blast radius is not the guard: **no `class` method call works under the seed
interpreter** on those two binaries. Anything measured with them is suspect.

## Cause 2 — the worker balloons to 29.4 GB RSS on the seed that gets past Cause 1

On `bin/simple` (12:58), Cause 1 does not fire and the worker instead runs away:

```
error: TIMEOUT: killed by kill_simple_monitor (rss=29451MB>=24000MB:
  .../simple run src/app/cli/native_build_worker.spl --source test/fixtures
  --entry-closure --entry test/fixtures/native_trailing_default_param/main.spl ...)
```

**Do not "fix" this with `KILL_SIMPLE_MEM_MB`.** The host has ~46 GB available and
runs ~15 concurrent lanes; raising the cap converts a contained guard failure into
a host OOM. 29 GB to compile a 60-line fixture is the defect.

## Cause 3 — the truncation path destroys the evidence (already filed, already in flight)

Every failing run ends with `error[E1002]: function \`TMPDIR\` not found`, which is
**not** a native-build error at all: it is `src/app/cli/native_build_main.spl`
failing to parse its own stderr-spill line, on the truncation path — i.e. the real
diagnostic is discarded precisely when it matters. Two nested double-quoted strings
inside one `{}` interpolation mis-lex (one is fine, two are not):

```simple
val a = "{id("HELLO") ?? "/tmp"}/x"   # -> error[E1002]: function `HELLO` not found
```

Already filed as `fstring_nested_quoted_literal_in_interpolation_misparsed_2026-08-17.md`
and `seed_fstring_nested_quote_interp_2026-07-17.md`, and a concurrent lane has an
**uncommitted fix in the working tree** hoisting `env_get("TMPDIR")` into
`spill_root`. Not touched here. This row records only that it masked Causes 1 and 2.

## What was NOT the cause

The relative-import `LBrace` parse error in
`src/compiler/70.backend/backend/vhdl_backend.spl:14,17,29` (`use .vhdl.x.{A}`)
is genuinely fixed upstream — but only in some binaries. It still fires on
`cargo-vhdl` (12:36) and not on `cargo-brk` (11:59), so a run on the wrong seed
misattributes the guard red to it. Same class of trap as Cause 1's table.

## Unblock condition

1. Settle which binary is origin/main tip and whether Cause 1 is a live regression
   or an artifact of two stale lane builds. Until then no `native-build` result
   from `/mnt/data/cargo-*/release/simple` is admissible.
2. Fix Cause 1 in `src/compiler_rust/compiler/src/interpreter*` (class receiver
   type resolving to `object`) and rebuild/redeploy the seed.
3. Profile Cause 2 — 29 GB for a 60-line fixture.
4. Land the in-flight Cause 3 fix so future failures report their real error.

Only then can the guard's actual subject (omitted trailing default parameters
across 6 call shapes) be evaluated at all.

## Do not

Weaken, narrow, or skip the guard. It is honestly red, and its `--selftest`
(8 fixtures) passes — the harness is sound; the tree under it is not.
