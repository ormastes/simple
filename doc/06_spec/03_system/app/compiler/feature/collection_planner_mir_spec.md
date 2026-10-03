# Collection planner MIR query legality

Authored companion; not generated execution evidence. Source:
`test/03_system/app/compiler/feature/collection_planner_mir_spec.spl`.

The scenarios call the production block canonicalizer on hand-built MIR.
They provide partial REQ-008 legality coverage, not compiler-driver wiring,
program execution, backend parity or optimizer performance evidence.

| Scenario | Input and asserted behavior |
|---|---|
| CP-MIR-01 | Two runtime-looking calls without ownership admission remain two calls; reuse counter stays zero. |
| CP-MIR-02 | Submitting generic `get` for admission cannot authorize reuse; both calls remain. |
| CP-MIR-03 | An explicitly admitted stable read becomes one call plus a copy from local 10 to local 11; reuse counter is one. |
| CP-MIR-04 | Reassigning the index between reads keeps both calls. |
| CP-MIR-05 | Overwriting the cached result between reads keeps both calls. |

Steps are `prepare MIR query fixtures` and `apply the production MIR query pass`.
Admission in the positive fixture is an explicit test-owned proof assumption.
It does not prove runtime ownership for production string-shaped MIR callees.
Run with an admitted self-hosted Simple test runner when available. These
scenarios are authored but unexecuted; no semantic RED/GREEN result is recorded.
