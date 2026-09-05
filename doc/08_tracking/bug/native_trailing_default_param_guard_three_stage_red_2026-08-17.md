# `check-native-trailing-default-param.shs` red — three stacked causes, none of them the trailing-default lane

- **Filed:** 2026-08-17
- **Status:** OPEN, narrowed to Cause 2 — Causes 1 and 3 no longer reproduce on the deployed 2026-08-17 12:58 seed; the guard now reports its REAL error (native-build worker timeout) with a fail-closed ERROR verdict
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

## Re-measured 2026-08-17 (guard-shape lane)

`bin/simple` = the deployed Rust seed built 2026-08-17 12:58 (59,537,240 B).

Guard harness, verbatim last stdout line:

    sh scripts/check/check-native-trailing-default-param.shs --selftest
    PASS — 8 selftest case(s) checked, all verdicts as expected            (exit 0)

    sh scripts/check/check-native-trailing-default-param.shs
    ERROR — nothing was checked: native-build was killed by a signal (exit 255; log saved to /tmp/check-native-trailing-default-param.3996613.log)   (exit 2)

Three things that were previously true are no longer true, all verified in this
checkout:

1. **The silent exit-1 is gone.** The guard emits an ERROR verdict line and
   exit 2 when there is no compiler; `SIMPLE_BINARY` is injectable and selftest
   case 1 (`no-compiler ERROR 2`) covers exactly that. Nothing further is owed
   on the guard-shape half of `native_trailing_default_param_guard_red_at_origin_tip_2026-08-15.md`.
2. **The static-receiver lowering fix is in the tree** — the widened guard
   `static_receiver_name == ""` is present in
   `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, and the run
   above shows no `undefined variable Widget`.
3. **Cause 3 (the TMPDIR interpolation masking the real error) is fixed** —
   `src/app/cli/native_build_main.spl:235` now hoists `val spill_root =
   env_get("TMPDIR") ?? "/tmp"` out of the interpolation, and the failing run
   above reports its REAL error instead of `function \`TMPDIR\` not found`:

       error: native-build worker timed out after 7200s before producing a binary.

   Also **Cause 1 does not reproduce on this binary**: the 8-line class-method
   repro prints `inline=10` under `SIMPLE_EXECUTION_MODE=interpreter` (it was the
   two stale `/mnt/data/cargo-*` lane seeds that failed).

What is left is **Cause 2 only**: the native-build worker does not finish
compiling a 60-line fixture — 29.4 GB RSS in the earlier measurement, a 7200s
worker timeout in this one. That is a compiler/native-build defect, not a guard
defect, and it is untouched by this lane. The guard is honestly RED (ERROR,
exit 2, fail-closed) and must stay that way until the worker is fixed. Do not
raise `KILL_SIMPLE_MEM_MB`, do not narrow the guard.

## Re-run on rebuilt seed 2026-08-17 (seed md5 669150b61f2f20401a6a895ae54e9fee, 59550432 bytes, mtime 2026-08-17 20:10:45)

    sh scripts/check/check-native-trailing-default-param.shs --selftest
    PASS — 8 selftest case(s) checked, all verdicts as expected        (exit 0)
    sh scripts/check/check-native-trailing-default-param.shs
    ERROR — nothing was checked: native-build was killed by a signal (exit 143)   (exit 2)

Cause 2 is UNCHANGED on the rebuilt seed. The guard again never reached a
trailing-default verdict: native-build was still running when the 3000s harness
timeout terminated it. No evidence for or against Causes 1/3 from this run
(they are gated behind the same native-build step). Record stays OPEN on
Cause 2 only.
