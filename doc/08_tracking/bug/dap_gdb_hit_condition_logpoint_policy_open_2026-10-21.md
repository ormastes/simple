# GDB DAP hit-condition and logpoint policy remains open

- Status: OPEN; full canonical row 09–12 remains HOLD.
- Tags: `workaround`, `underlying-fix`, `dap`, `gdb-mi`, `canonical09-12`.
- Bug database registration: PENDING; no admitted bug-add runner is available
  in this source-only session. This file is not evidence of a database insert.

The accepted assignment is `canonical_row_assignments["09-12"]` in
`/home/yoon/dev/robust-tdd-20261014/remaining-feature-assignments-20261021/assignments.json`:
DS6 GDB pipes and rich breakpoints, including preservation of condition/hit/log.
The frozen assessment at
`/home/yoon/dev/robust-tdd-20261014/uncoded-features-acceptance-audit-20261021/isa-safety/audit.json`
leaves DAP rich option mapping and logpoint policy unresolved and coordinated
by the root owner. These are local evidence paths, not portable repository links.

`src/app/dap/dap_handlers.spl` passes SourceBreakpoint condition,
hit_condition and log_message to `GdbMiAdapter.set_breakpoint_rich`.
The condition-only repair forwards the condition to the existing pipe client's
`set_breakpoint_full(location, condition, -1)`. Hit and log options continue
to be ignored for compatibility, so the numeric success response does not
demonstrate that their requested semantics were installed.

Current bounded workaround: use ordinary or conditional GDB DAP breakpoints
without hit conditions or log messages. This avoids relying on ignored
options; it does not implement the missing feature.

The underlying fix must select an explicit GDB DAP policy for the accepted
hit syntax and logpoint behavior. The local breakpoint manager accepts `N`,
`>=N`, `>N`, `<=N`, `<N`, `==N` and `%N`; these cannot all be represented by
the MI client's one-shot ignore-count flag. No such conversion or rejection
policy is selected here. Log interpolation, output delivery and whether a
logpoint resumes without stopping also need an accepted contract.

Acceptance for the future fix: exercise the actual DAP adapter and MI
transport for selected hit/log semantics; check emitted output and stop/continue
behavior, errors and ordinary breakpoint compatibility; retire this workaround
only after reviewed runtime evidence. Existing condition transport tests are
not coverage for these missing semantics.
