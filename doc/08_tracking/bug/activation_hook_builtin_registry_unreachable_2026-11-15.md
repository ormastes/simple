# Builtin sheets/slides registries unreachable after onCommand activation

Status: open
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
