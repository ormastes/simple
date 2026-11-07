# Windows Docker process-provider source review

Disposition: AWAITING_VERIFICATION. Reviewer: Astra; implementation sidecar: Sol.
Source baseline: `862d9e361534c1a13f83a2f43da06e07847df5af`.

Source review corrected host/image version-format conflation, operation-ID
contamination of the semantic digest/name, unconfirmed destruction, false probe
launch capability, missing post-mutation engine observation, short-lived start
handling, candidate-ID conflicts, exit-code parsing, Go-template brace escaping
and explicit mutable receiver/value write-back semantics.

Reviewed source includes policy/argv/digest contracts, canonical SDN codec,
bounded native/scripted execution, exact ownership observation and recovery.
The historical HCS intent builders remain but their probe, lifecycle and translated
capability no longer advertise execution. All source callers were inspected:
only the unit and cross-host system specs referenced that legacy provider.

Authored scenarios exercise concrete fields, exact command-vector matching,
nonzero exits, negative metadata, ownership recovery, ambiguous create and exact
absence. Their existence is not runtime evidence. Manual mirrors were reviewed
as authored descriptions; admitted docgen/sspec-maintain scores are unavailable.

Compiler/SPipe/native Windows tests, Windows fixture, performance measurements,
full core/MCP smoke and ordinary-client delegation qualification: NOT_RUN. The
parent's six-cycle compiler budget is exhausted. No Rust seed or install fallback
was used. Source whitespace and environment-facade guards are static hygiene only.

Residual limitations: caller owns durable intent/request journal and crash replay;
unknown-ID create and timed-out removal require external reconciliation; repeated
destroy may remain blocked. The minimal policy environment is explicit, but
executable path sealing and untrusted-client Docker pipe brokerage are not supplied.
The explicit controller/host Windows V2 dispatch source follow-up is owned by
those lanes and is not implemented by this provider commit.

## Common API follow-up

Reviewed additions route through the common Container API, normalize semantic
digests to raw64, add explicit managed scope labels, independently observe absence
and use shared launch-deadline admission without lifetime clipping. Native Windows
MachineGuid/architecture, lower-assurance boot counter, CNG service nonce and
bounded managed inventory are source implementations with authored negative specs.
The finite common factory explicitly refuses service continuity; persistent host
ownership/quarantine integration is the next separately owned dependency.
Captured native deadline/thread ownership is a separate reviewed commit/evidence
lane; its Linux native results do not qualify Windows execution.
