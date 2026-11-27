# Configured launch ownership admission

REQ-CMUX-004/005/008. **AUTHORED / NOT_RUN: nine cases, zero executed.** This is a source-authored manual, not generated or execution-qualified.

Every case calls the production pure `pane_configured_launch_admit` helper. It does not call a substitute native backend or assert fabricated process effects.

| Step | Expected source contract |
| --- | --- |
| Admit an empty bounded pane | Return its actual slot; retain zero incarnation and no child |
| Refuse a closing owner | Return an attributable error before allocation |
| Bind session/window/pane ancestry | Missing and mismatched owners refuse |
| Refuse an existing child | Preserve its identity and incarnation |
| Refuse deferred PTY cleanup | Preserve the exact pending token without calling it |
| Bound individual dimensions | Zero, negative, or over-limit dimensions refuse |
| Bound grid area | Product above 262144 refuses after individual dimension checks |
| Reserve both counters | Either exhausted content or child-incarnation counter refuses |
| Admit the last available counters | Admission does not itself consume an identity |

The synthetic PID and handle are pure record values only; no scenario passes them to an effect or cleanup function. These cases do not prove native open/spawn/close ordering, platform launch validation, failed-close retention, or public API publication. Those remain separate execution gates.
