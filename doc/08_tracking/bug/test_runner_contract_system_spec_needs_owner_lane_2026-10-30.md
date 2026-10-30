# test_runner_contract_system_spec is red outside the bootstrap owner lane (2026-10-30)

Status: OPEN. The spec stays RED outside the owner lane, with an explicit BLOCKED reason.

## Symptom

`test/03_system/app/test_runner/test_runner_contract_system_spec.spl` failed
0/4 in every ordinary lane (`simple test <spec>`, with and without
`--no-session-daemon`) with:

```
semantic: called unwrap on Err: compiled child requires nondelegating real execution
```

## Cause

Every scenario drives its child through
`test/support/compiled_child_authority_v1.spl`. That helper deliberately accepts
only the frozen `simple-bootstrap-command-owners-v3` receipt, plus
`SIMPLE_NO_BOOTSTRAP_DELEGATE=1` and `SIMPLE_NO_STUB_FALLBACK=1`. Only
`scripts/bootstrap/bootstrap-phase-verification.shs` publishes that receipt.
It has no source or seed fallback by design. Outside that lane the spec cannot
run. Before this change it reported a crash, so it looked like a regression.

## Handling

When `test_compiled_child_authority_v1("compiler_cli")` is refused, each
example calls `fail("BLOCKED: ...")` with the refusal reason and a link to
this record, then returns. It used to die on an opaque `unwrap`. In the
bootstrap phase-verification lane the authority is present, so the scenarios
run unchanged with the same assertions. No assertion was weakened.

`pending(...)` was tried first and rejected. Under the seed, the
`std.spec.pending` function shadows the BDD `pending` builtin and only prints,
so the enclosing `it` still counts as passed (`passed=4`). That is the
synthetic pass this spec's own third scenario forbids.

## Unblock condition

Close this record once the spec runs in an ordinary lane under one of these
conditions:

- the runner gains an owner-receipt lane that ordinary `simple test` can
  enter, or
- the operator contract gets a second, non-bootstrap child authority, for
  example the `SIMPLE_BINARY` that `test_runner_child_exec_spec` uses.

The same refusal affects the other consumers of the helper:
`test/03_system/app/mcp/mcp_stdio_contract_spec.spl` and
`mcp_stdio_crlf_and_malformed_recovery_spec.spl`.
