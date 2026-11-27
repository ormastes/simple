# Windows exec control probe pre-native rejection v3

Status: **SOURCE-ONLY NOT_RUN**. No compiler, tests, native connection or Docker
request was run. These source assertions are not Windows qualification evidence.

Spec: `test/01_unit/lib/nogc_async_mut/container/windows_docker_exec_control_probe_v3_spec.spl`.
Production source: `src/lib/nogc_async_mut/container/providers/windows/docker_exec_control_probe_v3.spl`.

The cases invoke the real begin_v3 factory with invalid inputs that must reject
before acquiring any native Engine connection. Fixture data reuses the shared
scripted adapter's request, policy, scope and baseline constructors only as
synthetic validation inputs. One additional case constructs the actual scripted
adapter through the common fixture factory and requires explicit rejection with
zero consumed scripted commands. No native observation is fabricated, positive
native admission is asserted, or caller readiness flag is used.
The structural baseline digest is neither actual host evidence nor authority.

| Case | Expected pre-native rejection |
| --- | --- |
| Scripted adapter provenance | Actual leaf entry refuses before installed-policy decoding or native connection; scripted command cursor stays zero |
| Different runtime operation | Shared complete-parent matcher rejects the operation mismatch |
| Different runtime engine | Shared complete-parent matcher rejects podman for the retained Windows Docker request |
| Different baseline machine | Native-machine metadata differs from the retained scope |
| Different request semantic digest | Plan digest differs from the correctly encoded native request bytes |
| Unsupported stream API | Installed wrapper hashing rejects stream API1.47 instead of the fixed1.48 profile |
| Different installed Docker generation | Request bytes and semantic digest are recomputed for the changed installed generation while retained plan/runtime generation stays fixed, isolating the scope-generation check |

Helpers are control_probe_fixture_v3(), returning request/expected/profile/
baseline, and control_probe_rejection_v3(outcome), returning the actual rejection
reason or an unexpected-owner sentinel. All Pending, Complete, Closed and
CleanupRequired owners are appended to a module retention array before any
assertion. A regressed factory therefore fails without discarding a native lease.
The array is cleanup retention only; copied entries must not be used as separate
logical readers. Rejected carries no owner or cleanup resource by contract.

These tests cover only invalid-input validation order and retained ownership on
unexpected outcomes. Actual CID observation, protected endpoint identity,
full installed-policy/container binding, async collection and the completed
control observation still require the common API live Windows fixture. No exec
create/start, one-use Host grant, durable birth or observed control pin is claimed.
