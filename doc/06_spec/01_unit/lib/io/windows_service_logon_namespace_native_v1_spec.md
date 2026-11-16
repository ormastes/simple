# Native service namespace V1 acceptance specimen

Status: **NOT_RUN**. Two source-authored real production API scenarios.
Source: `test/01_unit/lib/io/windows_service_logon_namespace_native_v1_spec.spl`.

Required setup: actual native Win64 runner on its canonical Windows thread,
actual dedicated Service5 logon, no impersonation, audit-compatible protected
current/global DOS directories, and direct nonremote/nonremovable global C:
volume with no current local C: override. Missing setup fails admission; no
skip, fake owner or unconditional success is present. No service provisioning
or Windows execution was performed in this source-only lane.

1. Open and step actual owner within8 turns; current and C: candidate succeed;
   copied owner observes same canonical authority. First close invalidates it,
   finite32-turn cleanup completes, and known closed alias reports completion.
2. Admit actual C: binding then request D:; exact second-drive diagnostic and
   current refusal demonstrate canonical quarantine, followed by actual close.

Every scenario registers owner immediately and after_each retries actual close
within32 turns. Native release failure causes an explicit failed assertion;
the source never turns failure into completion. A failed assertion cannot
promise process-lifetime cleanup if the external runner terminates abruptly.
Before a new admission, any previously retained fixture owner must complete
exact cleanup; otherwise admission fails without opening/overwriting it. The
second scenario unwraps actual C: admission before attempting D: substitution.

**NOT_COVERED**: injected native partial acquisitions/close failures, token or
namespace replacement, local drive override, hostile DACL/ACE changes,
cross-thread registry refusal, scheduler affinity, import/link validation,
real protected store paired-file comparison and child lifetime, stock OpenSSH
path preservation and authenticated remote exchange. Five separate pure cases
are not evidence for these native operations.
