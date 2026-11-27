# Container launch admission deadline

Authored manual mirror of
`test/01_unit/lib/common/contracts/container/effect_deadline_spec.spl`.
All five cases are **AUTHORED_UNRUN**, not execution evidence.

| Case | Required observation |
|---|---|
| Exact request, operation, action | Correct context returns the remaining window; each mismatched field refuses |
| Expiry and clock failure | Exact expiry, later time, and negative native sample refuse |
| Separate lifecycle authority | Stop, destroy, read, recovery, and unknown actions cannot be minted from a launch deadline |
| Public data validation | Modified contexts, malformed identity, duplicate/empty actions, and invalid expiry refuse |
| Integer bound | Maximum valid positive expiry subtracts without signed overflow |

These pure checks do not verify signatures, native clocks, governor scheduling,
or child execution. Final-exec enforcement also requires the shared process
owner checks and actual managed Linux/Windows consumers described in
`doc/05_design/container_launch_deadline_v1.md`. Running streams are not killed
and capacity is not freed merely because the launch window expires.
