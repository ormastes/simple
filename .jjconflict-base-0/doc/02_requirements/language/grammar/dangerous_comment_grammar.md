<!-- codex-impl -->
# Dangerous Comment Grammar Requirements

Date: 2026-04-23

## Selected Scope

Initial rollout is warning-first. Existing code must continue parsing, but placeholder, no-op, todo, dangerous-call, and wildcard escape hatches must produce visible rationale diagnostics when they are bare or weakly justified.

## Requirements

- REQ-DCG-001: `pass_todo`, `pass_do_nothing`, and `pass_dn` without a useful rationale shall warn as `REQC001`.
- REQ-DCG-002: `pass_todo("what remains", "hint or issue")`, `pass_do_nothing("why no-op is correct")`, and `pass_dn("why no-op is correct")` shall parse in statement and expression positions.
- REQ-DCG-003: `todo("what remains", "hint or issue")` shall be the canonical todo form; missing, one-argument, empty, or weak text shall warn as `REQC003`.
- REQ-DCG-004: Dangerous keyword calls from the registry shall require a useful first string rationale and warn as `REQC002` when missing or weak.
- REQ-DCG-005: `case _("why catch-all is correct"):` shall parse as a wildcard arm with rationale metadata.
- REQ-DCG-006: Plain `case _:` shall remain valid but warn as `REQC004` unless later analysis proves the arm is an explicit failure or unsupported path.
- REQ-DCG-007: Pure Simple and Rust Simple diagnostics shall use aligned warning codes `REQC001` through `REQC004`.
- REQ-DCG-008: Tree-sitter/editor query assets and generation guidance shall surface `pass_*`, `todo`, and wildcard rationale forms.

## Out Of Scope

- Deny-by-default strict mode.
- Full data-driven dangerous construct registry.
- Requiring issue-id formats for every rationale.
