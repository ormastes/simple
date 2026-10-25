# smux pane close discarded failed native teardown

Status: source repair candidate, **WARN / NOT_RUN**. No native execution yet.
Observed by independent source review against bee3e7b9f792; no claim that a
runtime failure was reproduced. Focused source repair cycle3.

`smux_close_pane` called `pane_release_best_effort` and unconditionally removed
the pane, updated geometry and returned true. That helper ignored the bool
result from `pty_close` or `process_close_piped`. A failed/deferred native close
therefore lost the authoritative handle and its retry route while reporting a
committed deletion. This contradicts existing checked session/window lifetime
and the mandatory Caret/CoreMux close/cleanup semantics.

The repaired public API keeps its bool signature. Its explicit-state pane owner
uses the existing checked child owner, now with an optional pane selector. Only
a record whose PTY and process authority have both been cleared may be removed.
False close retains exact native authority and a bounded pending intent; the
window's existing closing gates and poll projection prevent mutation during
partial cleanup. No provider result is synthesized or overridden.

Success removes the pane, preserves survivor rectangles without auto-growth,
chooses survivor focus when required, and invalidates that window's split
checkpoint. Last-pane deletion delegates checked window/session lifecycle,
including attachment, lease and notification cleanup. Last-pane retries validate
identity then continue checked deletion before generic closing refusal, avoiding
an infinite false-return trap after the first deferred close. Full owner kill
supersedes a pending pane intent only under its own installed closing marker;
it never discards the underlying failed handle.

Production scope: `src/os/apps/smux/api.spl`, `child_lifecycle.spl`, new
`pane_lifecycle.spl`. All native effects remain through existing Sosix owners.
The helper owns no global registry and the API remains the sole state committer.
The best-effort test reset helper is unchanged and must never serve as proof of
native cleanup.

Eleven authored executable cases and their evidence limits are documented in
`doc/06_spec/03_system/tools/smux_pane_lifecycle_spec.md`. Real pipe and ConPTY
positive scenarios are included, but all cases remain unexecuted. Actual native
false/deferred-close, final-pane retry and escalation receipts remain required;
pure retained-handle guards do not substitute for those provider observations.

The previous bee3 source manifest and materialization receipts are retained
historically; current readiness is marked STALE_AFTER_PANE_REPAIR. All55
receipt-owned alias changes remain untouched. Root will review, commit and repin
current source before any later execution. No compiler/helper/test run or
commit was performed for this source candidate.

Independent review cycle2 found three stale existing test oracles that expected
an empty live window after final-pane removal. They now require removed owner
inventories and exact protocol unknown-session errors. One separate pure-state
empty-window layout control preserves that guard without contradicting lifetime.
The two authored native cases now independently query their actual returned OS
PIDs before/after pane close and after session cleanup; registry removal alone
cannot satisfy their target-death assertion. The existing Sosix process facade
adds only an exact alias to its process_exists owner, with no new runtime ABI.
PID-query ambiguity and descendant/Job cleanup remain explicit evidence limits.

Cycle3 corrects that query binding: `process_is_running` has provider-specific
owned-handle/registry semantics and cannot uniformly consume these numeric PIDs.
The replacement `sosix_process_exists` aliases existing `process_exists` directly
to `rt_process_exists`. Both existing Windows C and Rust implementations query
arbitrary PIDs with OpenProcess and conservatively treat access denial as present;
there is no shell fallback. The fixture observes PID presence/absence separately
from registry removal and real command output. Actual linked-runtime provenance
remains a prerequisite, and retained process objects/PID reuse remain limits.
