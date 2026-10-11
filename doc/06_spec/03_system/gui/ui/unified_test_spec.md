# Unified UI backend fixture contract

Executable: `test/03_system/gui/ui/unified_test_spec.spl`.
Requirement: `REQ-SSPEC-SYSTEM`.

Status: **Phase1 seed diagnostics PASS, 3/3**. Evidence:
`build/phase-one-ui-diagnostic/unified_test_spec/cycle-one.log`. This is
headless bootstrap evidence; native qualification, measured coverage, and
automated docgen remain unverified.

1. Load `test/fixtures/ui/test_app.ui.sdn` through the production file parser.
   Render its state with both web and TUI-web HTML adapters. Each output must
   contain the action button, input placeholder, and ready label. A parse error
   fails the scenario.
2. Read both backend semantic snapshots. Require the fixture title and normal
   mode, a nonempty matching element inventory, and matching element identities,
   kinds, and text. Independently require the fixture's real action button.
3. Reload the fixture and send focus and input changes through the state owner.
   Both backend snapshots must report the focused input and its new value.
   Missing input nodes or value properties fail explicitly.

These headless scenarios exercise parser, state, renderer, and semantic adapter
integration. They do not prove live HTTP readiness, socket transport, browser
event delivery, or visible TUI-web rendering. Those remain required for broader
end-to-end UI qualification. Coverage annotations declare 80% targets; no
measured coverage is available.

The byte-identical legacy placeholder at `test/system/ui/unified_test_spec.spl`
was removed. Its local-constant assertions supplied no runtime evidence.
