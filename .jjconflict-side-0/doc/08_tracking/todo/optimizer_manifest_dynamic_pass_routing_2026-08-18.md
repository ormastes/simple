# TODO: Route dynamic manifest passes to a real execution path

Date: 2026-08-18
Area: src/compiler/60.mir_opt/optimizer_manifest.spl, optimizer_plugin.spl

Done in this change: nil/unknown PassKind no longer silently passes through the
plugin run adapters. `optimizer_plugin_run_on_function` / `_on_module` now
return `Result<..., text>` and fail closed with an error naming the pass and
the known MIR pass kinds when a MIR-scoped plugin's `mir_pass_kind` is nil
(e.g. any plugin built via `optimizer_plugin_from_dynamic_descriptor`).
Source-only plugins remain a typed Ok passthrough (they have no MIR pass by
construction). Spec:
`test/01_unit/compiler/mir/optimizer_plugin_passkind_fail_closed_spec.spl`.

Remaining (the manifest skeleton has no execution routing):

- `DynamicPassDescriptor.entry_symbol` is parsed, validated, and stored but
  never dispatched — there is no loader that resolves the symbol against the
  `simple.opt.mir.v1` ABI and invokes it. Until that lands, every dynamic pass
  reaching the run adapters correctly errors instead of running.
- `optimizer_plugin_from_dynamic_descriptor` should, once dispatch exists,
  carry a callable (or a routing token) instead of `mir_pass_kind: nil`, so
  the fail-closed branch applies only to genuinely unresolved kinds.
- Manifest pattern rules DO run (`run_manifest_pattern_rules_for_backend*`);
  only entry_symbol-based passes are unrouted.

Unblock condition: implement dynamic pass dispatch (resolve entry_symbol,
wrap as a runnable pass) and extend the run adapters to route it, keeping the
fail-closed error for anything still unresolved.
