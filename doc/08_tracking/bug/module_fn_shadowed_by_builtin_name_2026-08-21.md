# Module-level `fn` silently shadowed by an interpreter builtin of the same name

- Date: 2026-08-21
- Status: FIX IMPLEMENTED — VERIFICATION PENDING (deploy pending)
- Binary: `bin/simple` = Rust bootstrap seed (prints the seed warning banner)

## Symptom

`src/compiler/00.common/dynamic_identity/dense_tag_map.spl` originally declared a
module-level `pub fn freeze(...)`. Callers importing it got **the builtin
`freeze`** instead: the call returned its array argument unchanged, and a later
`match` on that value produced nil. It was renamed to `freeze_universe`
(`dense_tag_map.spl:169`) as a workaround. Per repo rule the workaround must not
be normalized silently — hence this record.

## Minimal reproduce

Fixture + spec (checked in, RED on purpose):

- `test/01_unit/compiler/frontend/name_resolution/builtin_name_shadow_fixture.spl`
- `test/01_unit/compiler/frontend/name_resolution/module_fn_shadowed_by_builtin_name_spec.spl`
  (mirrored under `test/unit/compiler/frontend/name_resolution/`)

```
timeout 300 bin/simple test test/01_unit/compiler/frontend/name_resolution/module_fn_shadowed_by_builtin_name_spec.spl
# Results: 4 total, 2 passed, 2 failed
#   expected [1, 2, 3] to equal 111      <- freeze
#   expected 3 to equal 222              <- len
```

## Neighbour table (same call shape, `pub fn NAME(xs: [i64]) -> i64` in another module, imported by `use`)

| module-level fn | interpreter (`bin/simple test`, `SIMPLE_EXECUTION_MODE=interpreter`) | JIT (`bin/simple run`) |
|---|---|---|
| `freeze` | **SHADOWED** — returns the array (frozen) | user fn wins (111) |
| `len`    | **SHADOWED** — returns 3 | **SHADOWED** — returns 3 |
| `push`   | user fn wins (333) | user fn wins (333) |
| `map`    | user fn wins (444) | user fn wins (444) |

`push`/`map` are array **methods**, not free-function builtins, so they are not
in `eval_builtin`'s `match` and do not collide. Any name in that `match` arm
list does collide.

## Precedence rule found (seed)

`src/compiler_rust/compiler/src/interpreter_call/mod.rs`:

- Priority 1 (`:447-466`): extern dispatch, with a hatch — a local definition
  beats a coincidental extern (`has_local_def`), fenced by
  `PRELUDE_UNSHADOWABLE` (`interpreter_eval.rs:373`, currently only `"exit"`)
  and warned for `is_user_facing_prelude` names (`interpreter_eval.rs:380`).
- **Priority 2 (`:480`): `builtins::eval_builtin(name, ...)` — unconditional.**
  No `has_local_def` check, no warning.
- Priority 3 (`:495`): BDD DSL.
- Priority 4: `functions.get(name)` — user functions, reached only if the
  builtin `match` returned `None`.

`freeze` is `builtins.rs:191`, `len` is `builtins.rs:171`. Neither is in
`PRELUDE_EXTERN_FUNCTIONS` (`interpreter_eval.rs:214`), so the Priority-1 hatch
never runs for them and Priority 2 wins silently — no diagnostic at all. This is
builtin-name precedence over user module functions, not an import/resolution bug.
The pure-Simple compiler (`src/compiler/**`) has no equivalent free-function
builtin table, so the fix belongs in the seed.

## Fix location + exact diff (NOT applied — seed build/deploy out of scope)

`src/compiler_rust/compiler/src/interpreter_call/mod.rs`, at the Priority 2 site
(line 480). Gate the builtin on the absence of a user definition, mirroring the
Priority-1 hatch and reusing its fences:

```rust
-        if let Some(result) = builtins::eval_builtin(name, args, env, functions, classes, enums, impl_methods)? {
-            return Ok(result);
-        }
+        // A user-defined function of the same name wins over a builtin, except
+        // for process-control names in PRELUDE_UNSHADOWABLE. Warn once so the
+        // shadowing is never silent.
+        let user_defined = functions.contains_key(name.as_str())
+            || FUNCTION_OVERLOADS.with(|cell| cell.borrow().contains_key(name.as_str()));
+        let builtin_wins = !user_defined
+            || super::interpreter_eval::PRELUDE_UNSHADOWABLE.contains(&name.as_str());
+        if user_defined && !builtin_wins {
+            warn_prelude_shadow_once(name.as_str(), functions, false);
+        }
+        if builtin_wins {
+            if let Some(result) =
+                builtins::eval_builtin(name, args, env, functions, classes, enums, impl_methods)?
+            {
+                return Ok(result);
+            }
+        }
```

Note the ordering trap: `eval_builtin` must not be *called* for a shadowed name —
several arms evaluate arguments and have side effects — hence the gate is on the
call, not on its result.

Unblock condition: seed rebuild + deploy, then the 4 specs above go green.

## Related

- `doc/08_tracking/bug/prelude_builtins_rebindable_by_transitive_import_2026-08-10.md`
  (the opposite direction: prelude names being shadowed *too* easily)
- `doc/08_tracking/bug/seed_native_build_unknown_extern_rt_array_len_safe_2026-07-12.md`

## Fix implemented 2026-08-21 (not deployed)

Applied in the Rust seed, both engines:

- Interpreter, `src/compiler_rust/compiler/src/interpreter_call/mod.rs`
  (Priority 2): the `builtins::eval_builtin` CALL is now gated on
  `builtin_wins_over_user_fn(name, user_defined)` (`!user_defined ||
  PRELUDE_UNSHADOWABLE.contains(name)`), reusing `warn_prelude_shadow_once`
  (warning limited to `is_user_facing_prelude` names, so a plain user function
  that matches no builtin does not warn).
- JIT/cranelift, `src/compiler_rust/compiler/src/codegen/instr/calls.rs`:
  new `sffi_alias_target_shadowed(name, user_defined)` gates the
  `len` -> `rt_len` (and sibling) alias mapping, which otherwise fired the
  `compile_inline_len` fast path BEFORE the `ctx.func_ids.get(func_name)`
  user-function branch.
- Rust unit tests added per engine:
  `interpreter_call::precedence_tests::user_defined_function_wins_over_builtin`
  and `codegen::instr::calls::tests::user_defined_function_wins_over_builtin_alias`.

Verification with the locally built (NOT deployed) binary
`/mnt/data/.cargo-target-shadow/release/simple`:

```
Results: 4 total, 4 passed, 0 failed
```
(was `Results: 4 total, 2 passed, 2 failed`)

`cargo test --release -p simple-compiler --lib`:
`test result: FAILED. 3693 passed; 54 failed; 2 ignored` vs the known baseline
`3677 passed; 68 failed` — no new failure attributable to this change (the
codegen gate is a no-op for any name absent from the alias table).

Unblock condition: seed rebuild + deploy to `bin/release/<triple>/simple`.

## Independent re-verification 2026-08-21 (still deploy-pending)

Re-ran the 4 specs on a seed freshly built from committed `main` content
(`src/compiler_rust/target/release/simple`, built for the `admit`/`assume`
contextual-keyword lane): `Results: 4 total, 4 passed, 0 failed`. The fix is
committed and correct; the deployed `bin/simple` is still the older seed, so
the remaining unblock condition is unchanged — a seed rebuild + deploy to
`bin/release/<triple>/simple`.
