# Builtin sheets/slides registries unreachable after onCommand activation

Status: verification-pending

## Root cause and fix (2026-11-15, branch work/caret-activation-bugdb-fix)

`extension_host_with_builtins()` has been genuinely lazy since 2026-07-31
(identical to `extension_host_with_builtins_indexed()`, no eager activate-all
loop), so no registry hook ran until an activation event fired. The two specs
asserted `is_active == true` immediately after construction, i.e. they were
stale against the lazy design (and contradicted the same file's later
"indexed host runs no activation hook" spec). The product code was correct:
firing the builtin's own `onCommand` (`activate_command`) populates the
registry. Fix: the two specs now assert the lazy pre-state, fire
`activate_command("sheets.function.double")` / `("slides.layout.titleDiagram")`
and then assert the same registry outcomes (assertions strengthened, not
weakened). RED: executed=10 passed=8 failed=2. GREEN: executed=11 passed=11.
Prevention spec (same file): every builtin with an activation hook runs it
when one of its own contributed commands activates.
Runtime/native unqualified (seed interpreter, Windows).

# Original report
Severity: P3
Found: 2026-11-15, lane `work/caret-tui-captures-20261115` (PR #9332)
Binary: seed interpreter, Windows

## Symptom

`activation_hook_spec` executed 0 until PR #9332 fixed private-fn visibility.
It now executes 10, passes 8, and fails 2 with `expected false to equal true`:

- "sheets DOUBLE is reachable via the function registry after activating the builtin through its own onCommand event"
- "slides title_diagram is reachable via the layout registry after activating the builtin through its own onCommand event"

## Notes

Making the registry `register` functions, `default_style` and
`cell_display_text` `pub` did not change the result, so this is not just
visibility. The likely causes are that the builtin's activation hook never
calls the register function, or that it registers into a different
module-state instance than the one the spec queries. The spec is correct and
must not be weakened.

## Unblock

The fix is done when `activation_hook_spec` reports 10/10. It also needs a
prevention spec showing that each builtin extension's onCommand activation
populates its registry.
