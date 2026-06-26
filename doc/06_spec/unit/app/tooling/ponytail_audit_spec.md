# Ponytail Audit Spec

Manual companion for `test/unit/app/tooling/ponytail_audit_spec.spl`.

## Scenarios

- Clean source returns a `Ponytail Audit` report with `status: ok`.
- Placeholder and abstraction markers return `status: review` with counts.
- Missing source returns `status: missing` with an explicit reason.
