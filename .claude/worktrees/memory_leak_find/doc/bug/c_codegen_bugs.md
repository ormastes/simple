# C Codegen Bugs — Bootstrap Compilation (2026-02-22)

Tracked during iterative bootstrap build: `.spl` → `.c` via `build/simple_codegen`.

**Stats:** 53 files compiled, 5 OK, 48 FAIL

---

## Bug Categories (by frequency)

### BUG-CG-001: Struct field access on wrong type (102 occurrences)
**Error:** `member reference base type 'long long' is not a structure or union`
**Cause:** Codegen emits `var.field` but `var` was stubbed as `long long` (import stub).
Imported struct types become `long long` stubs. Field access `.field` on `long long` fails.
**Fix:** Generate proper struct forward declarations for imported types, or emit accessor functions.

### BUG-CG-002: Docstring/comment leaks into code (69 occurrences)
**Error:** `expected ';' after return statement`
**Cause:** SDoc triple-quoted docstrings or inline doc comments parsed as code.
Lines like `Returns the value` appear as statements after `return`.
**Related errors:** `use of undeclared identifier 'Example'`, `use of undeclared identifier 'Returns'`, `use of undeclared identifier 'code'`
**Fix:** Strip docstrings/comments before codegen. The text-based parser doesn't skip `#` doc comments properly.

### BUG-CG-003: Missing expression in generated code (65 occurrences)
**Error:** `expected expression`
**Cause:** Various: empty match arms, incomplete translations, `pass_do_nothing` not handled.
**Fix:** Emit `0` or `(void)0` for empty expressions, translate `pass_do_nothing` to `(void)0`.

### BUG-CG-004: String/int type confusion (57 occurrences)
**Error:** `incompatible integer to pointer conversion` / `incompatible pointer to integer conversion`
**Cause:** Functions returning `text` (char*) stubbed as returning `long long`, or vice versa.
The codegen doesn't track return types of imported functions.
**Fix:** Add type annotations to extern function stubs, or use proper runtime declarations.

### BUG-CG-005: Import stub argument mismatch (26 occurrences)
**Error:** `too many arguments to function call, expected 0, have N`
**Cause:** Imported functions become `static long long fname(void) { return 0; }` stubs.
Actual calls pass arguments that don't match the stub signature.
**Fix:** Generate stubs with correct parameter counts, or use varargs stubs.

### BUG-CG-006: C keyword collision (12+ occurrences)
**Error:** `invalid parameter name: 'default' is a keyword` / `'short' is a keyword` / `'long' is a keyword`
**Cause:** Simple parameter names like `default`, `short`, `long` are C reserved keywords.
**Fix:** Mangle parameter names: `default` → `default_`, `short` → `short_`, `long` → `long_`.
**Files affected:** env_ops.spl, file_ops.spl, process_ops.spl, cli_parser.spl, cli_utilities.spl

### BUG-CG-007: Undeclared runtime functions (15+ occurrences)
**Error:** `call to undeclared function 'rt_*'`
**Functions:** `rt_process_run`, `rt_env_get`, `rt_time_now_unix_micros`, `rt_getpid`, `rt_hostname`, `rt_thread_available_parallelism`, `rt_volatile_read_*`, `rt_math_log`, `rt_file_exists`, `rt_cli_get_args`
**Cause:** `extern fn rt_*` declarations not emitted as C `extern` function declarations.
**Fix:** Emit `extern` declarations for all `rt_*` functions, or `#include "runtime.h"`.

### BUG-CG-008: Numeric separator not stripped (5 occurrences)
**Error:** `invalid suffix '_000_000' on integer constant`
**Cause:** Numeric literals like `1_000_000` not stripped of `_` separators in C output.
**Fix:** Strip `_` from numeric literals during codegen.

### BUG-CG-009: `exit` function conflicts with stdlib (3 occurrences)
**Error:** `static declaration of 'exit' follows non-static declaration`
**Cause:** Simple function named `exit` conflicts with C stdlib `exit()`.
**Fix:** Mangle function name to `simple_exit` or similar.

### BUG-CG-010: Unknown struct types (various)
**Error:** `unknown type name 'LeakCheckResult'`, `'DbFixResult'`, `'JitBackend'`, etc.
**Cause:** Imported struct/enum types not defined in the generated C file.
**Fix:** Generate forward declarations or type stubs for all imported types.

### BUG-CG-011: `pass_do_nothing` / `pass` not translated (10 occurrences)
**Error:** `use of undeclared identifier 'pass_do_nothing'` / `'pass'`
**Cause:** Simple keywords `pass_do_nothing` and `pass` not translated to C no-ops.
**Fix:** Translate to `(void)0;` or `/* no-op */`.

### BUG-CG-012: `error` function name collision (3 occurrences)
**Error:** `redefinition of 'error'`
**Cause:** Simple function `error()` collides with other definitions or itself.
**Fix:** Mangle to `simple_error` or use unique prefix.

### BUG-CG-013: Array literal return type mismatch
**Error:** `returning 'char[N]' from a function with incompatible result type`
**Cause:** String literals used where array return type expected, or vice versa.
**Fix:** Proper type mapping for array returns.

### BUG-CG-014: `len()` method not translated to function call (15 occurrences)
**Error:** `call to undeclared function 'len'`
**Cause:** `.len()` method calls on strings not translated to `simple_strlen()`.
**Fix:** Handle `.len()` method translation for all types (already done in real_compiler.c for some cases).

### BUG-CG-015: String method calls on wrong types (37 occurrences)
**Error:** `member reference base type 'const char *' is not a structure or union`
**Cause:** Method-style calls like `str.starts_with()` emitted as field access.
**Fix:** Translate string methods to function calls: `str.starts_with(x)` → `simple_starts_with(str, x)`.

---

## Priority Order for Fixes

1. **BUG-CG-007** (runtime declarations) — add `#include "runtime.h"` → instant fix for many files
2. **BUG-CG-006** (keyword collision) — simple rename: `default` → `default_val`, `short` → `short_flag`
3. **BUG-CG-008** (numeric separators) — strip `_` from numbers
4. **BUG-CG-009** (exit collision) — mangle `exit` → `simple_exit`
5. **BUG-CG-011** (pass keywords) — translate to `(void)0`
6. **BUG-CG-002** (docstrings) — strip doc comments
7. **BUG-CG-012** (error collision) — mangle `error` → `simple_error`
8. **BUG-CG-001/004/005/010** (struct types + stubs) — requires deeper codegen changes

---

## Files That Compile Successfully (5/53)

1. `app_compile_main.c` — 76 lines
2. `app_io_feature_ports.c` — 92 lines
3. `app_io_jit.c` — 64 lines
4. `lib_nogc_sync_mut_cli_mod.c` — 64 lines
5. `lib_nogc_sync_mut_cli_types.c` — 64 lines

These are small files with minimal imports and no complex types.
