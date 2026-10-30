# Smux live application-cursor test plan — 2026-10-26

Status: **AUTHORED / NOT_RUN**. This bounded source lane supports the selected
[REQ-CMUX-003](../../02_requirements/feature/caret_mux_tui.md) input contract.
It does not complete SendKeys, native backend compatibility or usable-replacement
qualification. The parent session restricted this lane to source work because
runtime explicit-library-mode qualification is blocked and the six-attempt
generator budget is exhausted pending an exception. No compiler, test executable,
SPipe generator, staging or commit is authorized in this lane.

## Production contract and ownership

`VtModes.application_cursor: bool = false` stores current child DECCKM state.
The constructor explicitly initializes it. `vt_application_cursor(screen:
VtScreen) -> bool` reads the live value and is exported by the canonical
`os.apps.smux.vt_screen` surface. Existing CSI parsing handles fragmented
`CSI ? 1 h/l`; mode dispatch updates only the live scalar. DECRQM 1 reports
set (`ESC[?1;1$y`) or reset (`ESC[?1;2$y`) through existing ordered replies.
Unknown modes retain their unknown response. RIS uses the existing constructor;
copies, resize, alternate-screen changes and synchronized-output handling retain
the current mode through existing value-state ownership. The mode is neither a
frozen visual attribute nor a reason to mark visual content dirty.

No host ABI, OS branch, configured family selection, input queue, capture history,
VT-v2 historical pin, capability flag or key encoder is changed. The root owns
integration and later independent review. Lower-model sidecars: N/A.

## Authored cases and traceability

Executable: [vt_application_cursor_spec.spl](../../../test/01_unit/os/apps/smux/vt_application_cursor_spec.spl).
Manual: [vt_application_cursor_spec.md](../../06_spec/01_unit/os/apps/smux/vt_application_cursor_spec.md).

| Case | Production assertion | Requirement support | Status |
|---|---|---|---|
| Default/query | False initially; exact eight reply bytes for reset | REQ-CMUX-003 | NOT_RUN |
| Fragmented set/reset | Final byte alone commits the mode; no visual dirtiness | REQ-CMUX-003 | NOT_RUN |
| Fragmented query | Exact set bytes and ordered set/reset replies | REQ-CMUX-003 | NOT_RUN |
| Unrelated modes | Nonprivate mode one and unknown private modes leave DECCKM intact | REQ-CMUX-003 | NOT_RUN |
| RIS | Resets live mode; unchanged blank content stays clean | REQ-CMUX-003 | NOT_RUN |
| Copies/replies | Derived reset does not change source; draining replies retains mode | REQ-CMUX-003 | NOT_RUN |
| Resize | Grow/shrink retain set state; later resize retains reset state | REQ-CMUX-003 | NOT_RUN |
| Alternate screens | Modes 47/1047/1049 share one live input mode | REQ-CMUX-003 | NOT_RUN |
| Synchronized updates | Live mode/replies change while visual frame stays frozen | REQ-CMUX-003; REQ-CMUX-005 regression | NOT_RUN |
| Mode-only publication | Unchanged visuals stay clean; resize retains live mode | REQ-CMUX-003; REQ-CMUX-005 regression | NOT_RUN |

## Deferred execution and admission

After the parent establishes an admitted runtime and authorizes bounded execution,
compile and execute the ten production-parser unit cases through the existing
SSpec workflow. Require actual case results, not loading/discovery. Then generate
the mirrored manual with SPipe, require zero stubs, and run the existing
SSpec-maintain scan. Review the full manual and preserve failures/unrun counts.
Reuse existing VT screen, history and capture regressions for integration; do not
rerun prior passing criteria without a changed implementation or new concern.

Primary manual flows are default/query, fragmented mode handling and live mode
during synchronized output. Edge cases are folded; executable SSpec is folded.
No capture artifacts are claimed: the oracle is actual parsed state and exact
protocol bytes. Runtime, native PTY/ConPTY, key encoding and performance evidence
remain absent. Independent source review cannot substitute for those gates.
