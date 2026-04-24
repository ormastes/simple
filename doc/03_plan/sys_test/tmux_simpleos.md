<!-- codex-system-test -->
# System Test Plan: `tmux_simpleos`

## Scope

This plan covers the first native `smux` backend for `tmux_simpleos`.

Included:

- session/window/pane lifecycle
- split-pane behavior
- attach/detach behavior
- input/output routing
- capture behavior
- compatibility-facing API shape
- error handling for invalid targets and missing shell/runtime
- observable metrics for startup and hot-path operation counters

Excluded from this slice:

- stock upstream `tmux` backend
- full tmux keymap parity
- mouse parity
- config-language parity

## Requirements

| Requirement | Description |
|-------------|-------------|
| REQ-001 | persistent session/window/pane model |
| REQ-002 | pane-backed shell execution |
| REQ-003 | attach/detach without session destruction |
| REQ-004 | split/layout operations |
| REQ-005 | input/output routing |
| REQ-006 | state query API |
| REQ-007 | capture API |
| REQ-008 | compatibility-facing tmux-shaped API |
| REQ-009 | native-first backend, no upstream tmux dependency |
| REQ-010 | backend swap readiness boundary |
| REQ-011 | explicit non-fatal failure handling |
| REQ-012 | declared deferrals remain deferred |
| NFR-007 | startup/operation observability counters are exposed |

## Execution

Focused design-level feature spec:

```bash
bin/simple test doc/06_spec/app/simpleos/feature/tmux_simpleos_spec.spl
```

Recommended adjacent checks once implementation exists:

```bash
bin/simple test test/system/os_shell_spec.spl
bin/simple test test/os/kernel/loader/executable_source_vfs_spec.spl
```

## Traceability

| Requirement | Test Cases |
|-------------|------------|
| REQ-001 | create session, create window, list panes |
| REQ-002 | pane starts shell backend and reaches running state |
| REQ-003 | detach preserves session, reattach restores visibility |
| REQ-004 | split horizontal/vertical creates new pane and updates geometry |
| REQ-005 | send text/command reaches target pane and capture shows output |
| REQ-006 | list sessions/windows/panes returns stable metadata |
| REQ-007 | capture returns visible/recent content and pane identity |
| REQ-008 | compatibility API functions map to native service behavior |
| REQ-009 | service works without checking host tmux availability |
| REQ-010 | backend contract can be queried independently of adapter surface |
| REQ-011 | invalid targets and launch failures return explicit errors |
| REQ-012 | deferred parity features are not required for pass |
| NFR-007 | metrics getter reports startup and operation counters |

## Pass Criteria

- every REQ has at least one passing assertion-based spec
- only built-in matchers are used
- no test requires host `tmux`
- failure paths prove containment rather than crash semantics
