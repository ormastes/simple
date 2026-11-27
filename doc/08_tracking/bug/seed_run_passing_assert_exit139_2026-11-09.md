# Seed exits 139 when `simple run` reaches a passing assert()

- **Priority**: P2
- **Status**: FIXED 2026-11-11 (lane seedB, verified at base 79d5af6723f6)
- **Repro**: `test/fixtures/repro/seed_run_passing_assert_exit139.spl`

## Observed (2026-11-09)

Binary: shared seed `C:/dev/simple/bin/simple.exe`, mtime 2026-11-04 16:58:52 +0900, size 40739328 bytes.

```
fn main():
    assert(1 == 1)
    print("after assert")
```

`simple.exe run <repro>` -> Segmentation fault, exit 139, nothing printed after the seed warning.
The same script without the `assert` line prints and exits 0.

## Expected

A passing assert is a no-op; the script prints `after assert` and exits 0.

## 2026-11-11 — FIXED at tip (lane seedB, worktree simple-p3-seedB-20261111, base 79d5af6723f6)

No longer reproduces; absorber identified.

**Live check, tracked seed `bin/simple.exe` (37584384 B, mtime 2026-11-11,
post-dates the failing 2026-11-04 40739328-byte binary named in this row):**

```
default:            run test/fixtures/repro/seed_run_passing_assert_exit139.spl
                    -> prints "after assert", exit 0
SIMPLE_EXECUTION_MODE=jit:      -> prints "after assert", exit 0
SIMPLE_EXECUTION_MODE=interpret: -> prints "after assert", exit 0
```

**Absorber:** PR #7597 (merge 9e7e7a526edb, 2026-11-07) — between the
2026-11-04 failing binary and this base. It added the statement-position
desugar of the call spelling `assert(COND[, MSG])` to `HirStmt::Assert`
(`src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`, with the
comment "never emit a bare C call that can bind libc's __assert") plus the
interpreter parity arm (`interpreter_call/builtins.rs`). Before it, the
statement call lowered to a bare call to the unresolved `assert` external,
which is the exit-139 jump-to-bad-address on a *passing* assert.

**Source-level pin (new, this lane):**
`src/compiler_rust/compiler/tests/seed_run_passing_assert_no_segv.rs`
exercises the exact statement shape through the static Cranelift JIT.
`cargo test -p simple-compiler --test seed_run_passing_assert_no_segv`
-> 2 passed, 0 failed.
