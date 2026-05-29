# Generic Syntax Repro Specification

## At a Glance

| Field | Value |
|---|---|
| Category | Feature / Language |
| Source | `test/feature/language/generic_repro_spec.spl` |
| Status | Active |
| Purpose | Promotes previously ad hoc generic syntax repros into scenario-based SPipe coverage. |

## Scenario Summary

| Metric | Count |
|---|---:|
| Active scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Behavior

This spec covers parser-safe generic syntax repros that previously lived in
top-level scratch files. It verifies that:

- methods dispatch through a generic type alias,
- generic instance method calls parse and execute,
- explicit generic function calls parse and execute.

Parser-sensitive forms that still fail SPipe parsing, including generic static
method calls and multi-parameter generic constructors, are tracked separately in
`doc/08_tracking/bug/generic_btree_spike_parse_dot.md` and preserved as a
non-executable fixture.

## Scenarios

- `dispatches methods through a generic type alias`
- `parses generic instance method calls`
- `parses explicit generic function calls`

## Verification

```bash
SIMPLE_LIB=src bin/simple test --force-rebuild test/feature/language/generic_repro_spec.spl
```
