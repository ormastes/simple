# An import that exists nowhere, called off the executed path, exits 0

- **Filed:** 2026-08-17 (measured 2026-08-18)
- **Lane:** USEWARN
- **Status:** OPEN — guard landed KNOWN-RED, policy change filed as a recommendation
- **Guard:** `scripts/check/check-undefined-import-run-exit-code.shs`
- **Component:** Rust SEED (`bin/simple` prints its own bootstrap-seed warning)

## The defect

`src/lib/gc_async_mut/gpu/engine2d/engine.spl:41` imported five functions that
existed nowhere in the tree and called all five (lines 1229/1234/1239/1244/1249).
The seed printed `[use-warning]` lines and **exited rc=0**. Any "it parses / it
runs" verification therefore passed over code that could not possibly work; the
real symptom appeared much later as `[jit-fallback] unresolved external symbol
... whole module dropped`. That instance is fixed. The exit-code hole is not.

## Minimal reproducer (verbatim, rc read directly — never through a pipe)

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 59,620,392 bytes,
mtime 2026-08-18 01:08:42 UTC. (The symlink target was replaced mid-session by
another lane; an earlier build behaved differently — see "Two shapes" below.)

```
use std.common.use_warning_probe.{uw_probe_zzz_absent}

fn never_called() -> i64:
    return uw_probe_zzz_absent(1)

fn main():
    print("REACHED")
```

```
$ bin/simple run repro2.spl >o 2>e ; rc=$? ; echo "RC=$rc"
RC=0
stdout: REACHED
stderr: [jit-fallback] unresolved external symbol 'uw_probe_zzz_absent': whole
        module dropped to the interpreter (expect ~100-1000x slowdown). ...
        [INFO] JIT compilation failed, falling back to interpreter: Cranelift
        JIT compile: Module error: unresolved external symbol ... would
        NULL-jump in JIT; deferring to interpreter
        [use-warning] 'uw_probe_zzz_absent' is named in `use
        std.common.use_warning_probe.{...}` but module '.../use_warning_probe.spl'
        does not provide it (imported from repro2.spl)
```

### Two shapes, and only one of them is fail-closed

Moving the identical call ONTO the executed path (into `main`) makes the same
binary add `error[E1002]: function \`uw_probe_zzz_absent\` not found` and exit
**1**. So an import that resolves to nothing is fatal only when execution
happens to reach it. The engine.spl shape — calls inside functions the entry
point never runs — is exactly the shape that stays silent. This is why "the file
runs and exits 0" proves nothing about the rest of the module.

## Where the downgrade happens

`src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:493`
— `fn warn_unprovided_use_names(...)`. Its only effect is the `eprintln!` at
**line 518**. It accumulates no error, returns nothing, and no caller can
observe that it found anything.

**Incidental, not deliberate.** The two early `return`s that carry comments
("opaque surface — not checkable" at :503, "not a `{...}` group import" at :507)
explain skipping the *check*. Nothing anywhere explains why a positive finding
should be non-fatal. There is no policy comment, no flag, no severity level.

## Why the existing guards do not cover it

| guard | why it misses this |
|---|---|
| `check-use-warning-oracle-deployed.shs` | proves the oracle still *speaks*; asserts nothing about exit codes |
| `check-error-line-with-zero-exit.shs` | matches `^[[:space:]]*error:`. The diagnostic here is `error[E1002]:` — a bracket at exactly the position that regex tests. Correct for its own shape; this is a second shape. And in the RED case above no `error` line is printed at all |
| `check-jit-unresolved-symbol-guard.shs` | unresolved *local variables* on the JIT lane, not `use`-imported names |

## Blast radius — UPPER BOUND, not a defect count

Not re-derived; `doc/08_tracking/bug/undeclared_imported_symbols_census.md`
already measures it rigorously: **1,226 deduped entries, 766 distinct undeclared
names, across 380 importing files** (§3), with a sampled false-positive rate of
**0/40 (0%)** for "declared nowhere" and a non-defect rate of **1/40 (2.5%)**
(one intentional tool-qualification negative fixture) (§5). Its predicate is
self-limiting against wildcard re-exports, `__init__.spl` aggregation, aliases
and package barrels, because a name provided by any of those is declared
*somewhere* and is filtered out.

Independent re-verification by this lane, 2026-08-18: 10 entries sampled from
Appendix A.1 (LIVE-AND-BROKEN, `src/`) re-checked with an anchored
declaration-shaped `/usr/bin/grep -rE` over all owned `.spl` **plus** a string
search over `src/compiler_rust/**` and `src/runtime/**` `.rs` for builtin
registration: **10/10 still have zero declarations and zero Rust registrations**
(`t32_cli_main`, `DASHBOARD_TABLE_DIR`, `count_nonempty`, `itos`,
`load_table_named`, `sum_int`, `today_date`, `write_table`,
`DASHBOARD_CACHE_PATH`, `load_table`). FP rate on this sample: 0/10. The census
stands.

**Labelled upper bound: <= 380 owned files can currently import a name that
exists nowhere and still exit 0** when the call sites are off the executed path.
That is a ceiling on exposure, not a count of confirmed silent-green runs.

## What was implemented vs filed

**Implemented** — `scripts/check/check-undefined-import-run-exit-code.shs`,
repo verdict convention (verdict LAST on stdout, `PASS — <n> ... checked` with
n > 0, FAIL 1, ERROR 2, zero-things-checked is ERROR). Three fixtures from one
run: a CONTROL that must run and exit 0 (a dead harness yields ERROR, never
PASS), the on-path undefined call (currently GREEN, rc=1), and the off-path
undefined call (currently **RED**, rc=0). Fatal `--selftest` with four stub
binaries in both directions — fail-open stub must FAIL, its exit-code MUTATION
must PASS, a SIGSEGV stub must FAIL, a broken-control stub must ERROR.
Current verdict on this host:
`FAIL — 3 fixture(s) checked ..., defect(s): unreached-undefined-import-exits-0`.

**Filed, not implemented** — making an unprovided `use` name a hard error at
`module_loader.rs:493`. With <= 380 owned files exposed, flipping the severity
would turn an unknown but large number of currently-green lanes red in one step,
inside the Rust seed, which cannot be validated without a rebuild this lane is
forbidden to do. The staged path is: keep the guard red, drive the census
backlog down, then flip severity. A cheaper intermediate that needs no census
work is to reuse the existing `SIMPLE_JIT_STRICT=1` escalation the jit-fallback
line already advertises, and make the off-path case honour it.
