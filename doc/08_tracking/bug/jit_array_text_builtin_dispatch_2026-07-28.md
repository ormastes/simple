# JIT array/text builtin dispatch defects (2026-07-28)

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).

Engine under test: **Cranelift JIT** (`bin/simple run`, `SIMPLE_EXECUTION_MODE=jit`).
Reference semantics: the tree-walk interpreter (`SIMPLE_EXECUTION_MODE=interpreter`),
correct in every case below.

Companion measurement table: `run_vs_test_harness_divergence_2026-07-28.md`.
Note that `bin/simple test` hard-defaults to the interpreter, so **no spec in the
suite can catch any of these** — they are only reachable via `bin/simple run`.

Binary identity for all evidence in this file: `bin/simple` currently resolves to
`bin/release/x86_64-unknown-linux-gnu/simple`, which **prints the Rust bootstrap
seed warning** — i.e. the deployed default tool is the seed, not the pure-Simple
self-hosted binary, contrary to `.claude/rules/bootstrap.md`. That is itself worth
a separate ticket; it also means these are seed-JIT defects and are fixed in
`src/compiler_rust/`.

---

## FIXED in this change

### 1. `to_*` prefix test swallowed non-cast methods and returned the receiver unchanged

**Severity: highest — silent, plausible, data-corrupting, exit 0.**

Two dispatch sites gated the numeric-cast lowering on a *prefix* test:

```rust
if method.starts_with("to_u") || method.starts_with("to_i") || method.starts_with("to_f")
```

Any method sharing those three prefixes entered the cast branch, matched no arm of
the inner `match`, and fell to a wildcard that returned the receiver **unchanged**:

- `codegen/instr/closures_structs.rs` — `_ => return Ok(Some(receiver_val))`
- `codegen/instr/methods.rs` — `_ => from_ty`, which makes `to_ty == from_ty` and
  takes the `from_ty == to_ty => receiver_val` passthrough.

Captured non-cast names, with owned-source call-site counts:

| method | sites | was |
|---|---:|---|
| `to_index` | 123 | receiver returned unchanged |
| `to_upper` | 52 | `"hello".to_upper()` → `"hello"` |
| `to_int_or` | 34 | receiver returned unchanged |
| `to_utf8` | 9 | receiver returned unchanged |
| `to_feature_string` | 9 | receiver returned unchanged |
| `to_iterable` | 5 | receiver returned unchanged |
| `to_unix_timestamp` | 4 | receiver returned unchanged |
| `to_id`, `to_import`, `to_uppercase`, `to_include` | ~9 | receiver returned unchanged |

`to_include` is a spec matcher, so this also silently no-opped assertions.

Why it presented as "`to_upper` broken but `to_lower` fine": `to_lower` starts with
`to_l`, misses the prefix test, and reaches the correct
`"to_lower" | "lower" => "rt_string_to_lower"` table arm. The alias `.upper()`
likewise works. Only the canonical `to_upper` spelling was hit.

**Fix applied:** replaced both prefix tests with an exact allowlist
(`let numeric_cast_target = match method { "to_u8" => Some(TypeId::U8), ... _ => None }`)
so non-cast names fall through to the normal builtin/user-method resolution, where
`to_upper` is already mapped to `rt_string_to_upper`.

### 2. `arr.enumerate()` — runtime function existed, dispatch arm did not

`rt_array_enumerate(array) -> RuntimeValue` has always existed in
`runtime/src/value/collections.rs` (returns `(index, item)` tuples, matching the
interpreter) but neither dispatch table had an `"enumerate"` arm, so the call fell
through to `rt_method_not_found` and returned an error value while exiting 0.

**Fix applied:** added `"enumerate" => "rt_array_enumerate"` to both tables.

### 3. `text.strip()` — missing alias of `trim`

The interpreter treats `"trim" | "trimmed" | "strip"` identically
(`interpreter_method/string.rs`). The JIT tables only had `"trim"`.

**Fix applied:** `"trim" | "trimmed" | "strip" => "rt_string_trim"` in both tables.

---

## FILED — not fixed here

### 4. `arr.map(...)` — `rt_array_map` does not exist

- **Dispatch table lacking the arm:** neither
  `codegen/instr/calls.rs` (string/array symbol match, ~line 3238) nor
  `codegen/instr/closures_structs.rs` (`try_compile_builtin_method_call` symbol
  table) can resolve it, because there is no symbol to resolve to.
- **Symbol name that would be needed:** `rt_array_map`.
- **Fix shape:** add
  `pub extern "C" fn rt_array_map(array: RuntimeValue, closure: RuntimeValue) -> RuntimeValue`
  to `runtime/src/value/collections.rs`, modelled directly on the adjacent
  `rt_array_filter` (same `rt_closure_func_ptr` + `transmute` + call-per-element
  shape, but pushing `func(closure, *item)` instead of the item). Then add
  `"map" => "rt_array_map"` to both dispatch tables. Reference semantics:
  `interpreter_method/collections.rs`.
- 1,095 call sites in owned source.

### 5. `text.lines()` — `rt_string_lines` does not exist

- **Symbol name that would be needed:** `rt_string_lines`.
- **Fix shape:** add `rt_string_lines(text) -> RuntimeValue` to the runtime
  returning an array of lines, then add `"lines" | "split_lines" => "rt_string_lines"`
  to both tables. The interpreter's arm is
  `"split_lines" | "lines"` in `interpreter_method/string.rs:204` — mirror its
  trailing-newline handling exactly rather than reusing `rt_string_split`, whose
  arity (needs a separator argument) does not fit the zero-arg call shape the
  on-demand declaration path builds.
- 79 call sites.

### 6. `filter` / `any` / `all` SIGSEGV, and `any`/`all` ignore their predicate

Two distinct defects behind one symptom.

**6a — arity/semantic mismatch (definite).** The runtime signatures are:

```rust
pub extern "C" fn rt_array_any(array: RuntimeValue) -> i64   // NO predicate
pub extern "C" fn rt_array_all(array: RuntimeValue) -> i64   // NO predicate
```

They are "is any/every element truthy", not "does any/every element satisfy `f`".
The dispatch tables map `"any" => "rt_array_any"` / `"all" => "rt_array_all"` and
the on-demand declaration path in
`closures_structs.rs::try_compile_builtin_method_call` builds the signature as
`args.len() + 1` I64 params — so a one-argument `arr.any(\x: ...)` is declared with
**two** params against a **one**-param callee, and the predicate is silently
discarded even when it does not crash. **Fix shape:** either add
`rt_array_any_by` / `rt_array_all_by` taking `(array, closure)` and route the
1-arg form to those (keeping the 0-arg form on the existing symbols), or give the
existing symbols a closure parameter and update the 0-arg callers. The predicate
form must not share a symbol with the truthiness form.

**6b — the SIGSEGV itself (root cause NOT yet isolated).** `rt_array_filter` *does*
take a closure and is null-guarded (`rt_closure_func_ptr` returns null for any
non-Closure heap value, and filter then returns an empty array), so a malformed
closure value cannot by itself explain the crash. The remaining candidates are
(i) closure *construction* in the JIT, or (ii) an ABI mismatch when
`rt_array_filter` `transmute`s `func_ptr` to
`extern "C" fn(RuntimeValue, RuntimeValue) -> RuntimeValue` and calls into the
JIT-compiled lambda body. **Next step to discriminate:** run a lambda that is
never passed to a builtin (`val f = \x: x * 2` then `f(21)`) under
`SIMPLE_EXECUTION_MODE=jit` in its own file. If that alone crashes, the defect is
closure construction/ABI and is upstream of every closure-taking builtin; if it
succeeds, the defect is in the runtime's call-into-JIT edge.

### 7. Unresolved method calls print to stderr and still exit 0

`rt_function_not_found` / `rt_method_not_found`
(`runtime/src/value/sffi/error_handling.rs`) `eprintln!` and then return
`RuntimeValue::from_special(tags::SPECIAL_ERROR)`. Execution continues and the
process exits 0, so a missing builtin is indistinguishable from a correct run for
any caller checking `$?` — this is what made items 4 and 5 above silent wrong
answers rather than loud failures.

**Fix shape (deliberately not applied here):** make these set a process-global
"runtime error occurred" flag that the driver consults to exit non-zero, rather
than `abort()`ing at the call site — an abort would convert today's silent wrong
answers into crashes inside currently-passing runs. This is a *behaviour change
with broad blast radius*: every program that today limps past a missing builtin
would start failing, which is correct but should land deliberately and with the
suite re-baselined. Recommend landing it immediately **after** items 4, 5 and 6,
so the newly-loud failures are ones that have already been fixed.

---

## Verification note

`bin/simple test` cannot verify any of this — it hard-defaults to the interpreter
and `TestExecutionMode` has no JIT variant. So regression coverage has to come
from either Rust-level codegen tests or scripted `bin/simple run` invocations.

**The existing codegen harness cannot catch this bug class.** There *is* a
`shared_method_static_to_upper` test in
`compiler/src/codegen/codegen_shared_tests/string_method_tests.rs`, and it passed
throughout — because `cranelift_only_test!` expands to `cranelift_ok(...)`, whose
entire assertion is that `codegen.compile_module(&module)` returns `Ok`:

```rust
codegen.compile_module(&module)
    .unwrap_or_else(|e| panic!("cranelift compilation failed for {}: {:?}", name, e));
```

It never executes the compiled code and never inspects a result value. A lowering
that silently emits the receiver unchanged compiles perfectly, so it passes. The
test's receiver is even a `ConstInt 0` rather than a string. Any real guard for
defect 1 must **run** the generated code and compare against the interpreter;
adding more `cranelift_only_test!` entries would add coverage in name only.
