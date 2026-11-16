# DAE-02 generic SDK readiness safety correction

Scope: root's selected safety repair for the existing legacy callback API.
This is a partial DAE-02 correction, not a new daemon recovery framework.

| Requirement | Required behavior | Authored executable evidence |
| --- | --- | --- |
| REQ-DAE02-SDK-SAFETY-001 | A failed readiness ping returns false without signalling the PID-file target, rewriting its lock, or starting a replacement. | `daemon_sdk_owned_sentinel_safety_v1_spec.spl`: existing live sentinel and post-start failed probe, sync and async |
| REQ-DAE02-SDK-SAFETY-002 | Startup is attempted at most once; a false startup result returns false without ping or recovery, even if the callback published a live PID. | `responsive_safety_v1_spec.spl`: startup refused, both facades; owned-sentinel startup-refusal cases |
| REQ-DAE02-SDK-SAFETY-003 | Sync and async public APIs preserve the same fail-closed backend behavior and existing signature. | Both suites exercise both actual exported entrypoints |
| REQ-DAE02-SDK-SAFETY-004 | A successful ping of an already running daemon returns true without calling startup; disappearance during failed ping does not authorize replacement. | Callback success/disappearance cases, both facades |
| REQ-DAE02-SDK-SAFETY-005 | Preserve the separate app readiness path and accurately document its non-destructive behavior. | Source call-chain evidence and corrected resource-governor design; no app source change |

Spec paths: `test/02_integration/lib/daemon_sdk/responsive_safety_v1_spec.spl`
and `test/03_system/tools/daemon_sdk_owned_sentinel_safety_v1_spec.spl`.

Evidence status: AUTHORED_NOT_RUN. Root prohibited runtime/build/native campaigns
for this source lane. Native fixtures must use the actual admitted self-hosted
runtime and owned-process provider; unsupported capability must fail rather than
substitute a seed, a fake owner, or another process.

There is no new recovery grant, retry policy, process adoption, public owner
constructor, runtime export or second journal. A future explicit restart API
must accept and retain genuine process/service ownership and observe its actual
cleanup; config, PID and callbacks cannot supply that authority.
