# Bootstrap callable ABI receiver accounting rejects valid calls

**Status:** fixed in the frozen worktree; focused Rust verification passed.
**Observed:** 2026-08-15.

Retained evidence:
`build/mini_builds/phase4_tools_rust_seed/fresh/bootstrap_main.log`.

Five Simple files fail under two repeated callable-ABI shapes:

- instance `HostTaskHandle.join`: target metadata declares one parameter while
  the validator counts one explicit argument plus one receiver slot;
- free `eval_expr`: target metadata declares one parameter while the call has
  two explicit arguments and no receiver.

The failures fan out across CUDA mapping, MIR lowering, backend environment,
and execution helpers, so per-caller source edits would be a shortcut.

## Root cause and fix

Both diagnostics were correct fail-closed symptoms of suffix-only receiver
method resolution selecting an ABI-incompatible callable:

- erased `[text].join(", ")` was stolen by the only linked same-tail instance
  method, self-only `HostTaskHandle.join()`;
- `self.backend.eval_expr(expr, ctx)` was stolen by the unrelated same-tail
  free function `compiler.frontend.core.interpreter.eval.eval_expr(eid)`.

The shared Cranelift owner now filters suffix-only receiver candidates before
selection: the candidate must be `Instance`, have recorded ABI metadata, and
declare at least receiver + explicit-argument slots. Bare one-argument `join`
also enters the existing tag-dispatching builtin path before name lookup, as
`try_compile_builtin_method_call` already maps it to `rt_string_join`.

Focused tests cover the exact HostTaskHandle theft, a valid self+argument
instance target, the exact free-function theft, missing metadata, and join's
accepted/rejected arities. Stub fallback remains disabled.

## Focused evidence

Each exact library filter ran once after the shared `node_exec.rs` test
scaffolding compiled cleanly:

- `erased_join_uses_builtin_dispatch_before_host_task_join`: 1 passed;
- `suffix_method_candidates_require_instance_receiver_and_compatible_arity`:
  1 passed;
- `cross_module_dynamic_receiver_rejects_same_tail_free_function`: 1 passed.

Retained logs are
`build/native_probe/stage4-callable-abi-erased-join-final.log`,
`build/native_probe/stage4-callable-abi-candidate-filter-final.log`, and
`build/native_probe/stage4-dynamic-receiver-free-theft-focused-lib.log`.

Provider token usage and comparable completed-bug average: unavailable.
