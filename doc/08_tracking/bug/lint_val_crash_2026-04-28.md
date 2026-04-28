# Bug: lint and fmt crash on any file with a `val` declaration

- **Filed:** 2026-04-28
- **Severity:** High — `bin/simple lint` and `bin/simple fmt` are unusable across the working tree
- **Status:** Open

## Symptoms

Running `bin/simple lint <file>` or `bin/simple fmt <file>` on a `.spl` file
that contains any `val` declaration prints a runtime error and segfaults
(exit code 139).

```
$ bin/simple lint /tmp/m14.spl
Runtime error: Function 'line' not found
Segmentation fault (core dumped)
```

`bin/simple fmt` fails the same way with a different missing symbol:

```
$ bin/simple fmt --check /tmp/m14.spl
Runtime error: Function 'extend' not found
FAIL /tmp/m14.spl needs formatting
```

`bin/simple check` (which runs lint+fmt in parallel) reports both:

```
=== Running Lint + Format (parallel) ===
Lint failed (exit code -1)
Format check failed (exit code -1)
```

## Minimal reproducer (3 lines)

```spl
fn _foo(x: u64) -> u64:
    val y = x
    y
```

Replacing `val` with `var` makes the crash disappear.

## Discrimination matrix

| Body                                | Result |
| ----------------------------------- | ------ |
| `var y = x`                         | OK     |
| `val y = x`                         | CRASH  |
| function with no body / single expr | OK     |
| empty file                          | OK     |
| `var` declarations only             | OK     |

## Investigation log

1. `bin/simple build lint` → silent no-op (per existing memory note
   `feedback_extern_bootstrap_rebuild.md`).
2. `bin/simple lint <file>` runs the Rust handler `run_lint` in
   `src/compiler_rust/driver/src/cli/code_quality.rs:724`.
   `dispatch_to_simple_app` does **not** include `src/app/lint/main.spl` in its
   whitelist (`src/compiler_rust/driver/src/main.rs:989`), so the dispatch
   always falls through to the Rust handler. `SIMPLE_LINT_RUST=1` and
   `--json` give identical crashes.
3. `Runtime error: Function 'X' not found` originates from
   `rt_function_not_found` in
   `src/compiler_rust/runtime/src/value/ffi/error_handling.rs:39`. It is
   reachable from two sites:
   - JIT-emitted fallback in
     `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:514,540,550`
   - interpreter extern dispatch
     `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1256` →
     `ffi_value::rt_function_not_found_fn` → same runtime symbol.
4. Bisecting `src/os/crypto/sha256.spl` narrowed the trigger to lines 137–146
   (the first `_sha256_compute_padded_len` function). Further reduction
   isolated `val <name> = <expr>` as the sole trigger.
5. Both the current `bin/release/x86_64-unknown-linux-gnu/simple` (Apr 27)
   and `simple.bak.sigsegv` (Apr 24) reproduce. The bug is in source, not a
   build artifact.

## Confirmed root cause (gdb verification)

The compiler is lowering field access as a global-name function call.

### Precise call site (disassembled)

`io__cli_commands__cli_run_lint+2126..+2143` in
`bin/release/x86_64-unknown-linux-gnu/simple`:

```
0x46f419: lea  "line\0" → %rdi          ← function name to look up
0x46f427: mov  %r13, %rsi               ← name length 4
0x46f42a: call rt_function_not_found    ← unconditional fail
0x46f42d: rt_value_to_string(rax)
0x46f437: rt_string_concat(prev, that)
```

Memory at `0xfef76c` decoded (via `gdb x/s`) is the literal string
`"line"`. The compiler emitted a **direct, unconditional** call to
`rt_function_not_found("line", 4)` for the `result.line` expression
in this `print` at `src/app/io/cli_commands.spl:219`:

```spl
print "{file_path}:{result.line}: {level_text}[{result.lint.code}]: {result.lint.message}"
```

The same pattern produces the "extend" error in `fmt`.

### Why `val y = 1` triggers it but `var y = 1` does not

The `rt_function_not_found("line")` call is inside the `for result in
results:` body of `cli_run_lint`. It only executes when `results` is
non-empty. Empirically (gdb breakpoint on `rt_function_not_found`):

- `val y = 1` → break fires → `results` was non-empty
- `var y = 1` → no break → `results` was empty

So *some rule* in `check_all_rules` produces a finding for `val y = 1`
that I haven't isolated. None of the visible rules in the std
`check_all_rules` (in `src/lib/common/tooling/easy_fix/rules.spl:42`)
should match a single `val y = 1` line — text-search shows only
`check_resource_leak` examines lines starting with `val `, and it
requires `= open(` / `= connect(` / `= File.open(` to fire. So either
(a) some other rule in the list does match in a way I haven't traced,
or (b) the linter's own `check_line` produces a result for plain
`val ...` lines via a path I haven't found. Confirming the exact
producer needs an instrumented build.

The print loop simply *exposes* a pre-existing codegen bug: every
result triggers the broken `result.line` lowering.

### Why the codegen bug doesn't fire for `result.lint.code`

`code` resolves to the global data symbol `cli__main__code`
(`val code = 0` at `src/app/cli/main.spl:13`), so the same
field-as-name lookup *succeeds* — it loads `0` from the data section.
The result is silently wrong (every line number prints as `0`-ish
garbage), but it doesn't segfault. `line`, `extend`, and
`is_uppercase` have no shadow global, so they hit the
`rt_function_not_found` fallback and the program then dereferences the
error sentinel and segfaults.

### Where the codegen falls through

The `rt_function_not_found` fallback emit sites in
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`:514,
540, 550 are the most likely culprits — they produce direct calls to
`rt_function_not_found` when the compile-time lookup for a name fails.
Field access on a struct should never reach this path; it should emit
a struct-offset load. Something in the type-resolution/lowering for
`Property`/`MemberAccess` AST nodes is failing to find the field
definition and falling through.

## Real fix vs. workaround

**Real fix:** trace the lowering for `Property`/`MemberAccess` in
`src/compiler_rust/compiler/src/codegen/instr/methods.rs` and
`closures_structs.rs`. When the receiver's type is statically known
(`LintResult`, `Replacement`, `LineContext`), the lowering must
resolve to a struct-offset load, not a name-based call.

**Pure-Simple workaround attempted and FAILED (2026-04-28):**

Two source-level workarounds at `src/app/io/cli_commands.spl:219` were
tried and rebuilt via `scripts/bootstrap/bootstrap-from-scratch.sh
--deploy`. Both crashed:

1. Extract field accesses to locals before interpolation (`val rline =
   result.line` etc.) → same `Function 'line' not found` crash. The
   broken lowering applies to assignment too.
2. Call `result.format()` (which already exists on `LintResult`) →
   dispatched to `backend::vhdl_constraints::VhdlConstraintError::format()`
   instead of `LintResult::format()`. Hard SIGSEGV in `rt_string_concat`.

The bug is deeper than per-expression lowering: the **loop-variable
type is stripped**. `for result in results:` where `results: [LintResult]`
binds `result` with no static type, so any field/method access on
`result` falls through to name-based dynamic dispatch.

This means there is **no Pure-Simple workaround at the call site**.
The fix has to be in the codegen — either preserve loop-element type
info, or make `Property`/`MemberAccess` lowering refuse to fall
through to dynamic name lookup on a typed receiver.

**Do NOT** add `val line = 0` / `val extend = 0` / `val is_uppercase = 0`
shims. They would silence the SIGSEGV but ship silently-wrong output
because every field access would return `0`.

## Workarounds

- `bin/simple lint --fix-dry-run <file>` does not crash (parser failure
  short-circuits the lint passes).
- Replacing `val` with `var` in the file under test is not a real workaround
  because the codebase makes heavy use of `val`.
