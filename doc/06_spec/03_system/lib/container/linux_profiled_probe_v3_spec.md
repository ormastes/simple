# Linux CPU profiled probe V3 — manual evidence plan

**Status: AUTHORED_NOT_RUN.** The executable fixture requires a provisioned
administrator-installed Linux fresh workspace, a pinned Podman/image/runtime,
a real provider CLI, and the explicit fixture inputs listed below. No result
from this authored spec is execution evidence.

## Evidence class and limits

This is a real host-fixture scenario, not a model. It opens the installed
workspace root and passes the original common owner through the public probe
API. It is CPU-only. It does not exercise GPU admission, mounts, a grant
service, synthetic native-owner inputs, or native fault injection. The
profiled collector must obtain its own actual `Wait`, `Logs` EOF, combined
capture evidence, and post-configuration from the retained owner.

The profile selection and collector use an actual provider name decoded by
`decode_provider_cli_provider_v1`; the fixture must provide a request whose
compiled command matches profile index zero (`--version`) for that provider.
The request and template are read from regular no-follow files with bounded
reads. The root opener supplies the installed principal and original storage
owner. The fixture does not manufacture authorization from a provider label.

The public V3 probe calls retain the exact updated owner before the spec reads
their response. The start helper's completion is not interpreted as a
`Running` receipt. Stop, Remove, and whole-cohort Absence must complete before
the same-writer settlement call. The test then asks the actual root cleanup
turn to close retained resources.

Each helper driver establishes one absolute monotonic deadline before its
operation, retains that same deadline across all steps, and yields with
`sleep_ms(1)` between pending steps. The drivers are capped at 65,536 turns;
clock failure or deadline expiry stops the scenario with the current root
owner retained. The collector's original deadline is passed unchanged into
every collector step. Its returned cursor and common owner are stored before
reading the returned error or receipt, so a failed or expired collection stays
available for explicit continuation/cancellation. The fixture does not
automatically close or settle after a pending/error result.

The receipt assertions cover its actual combined-capture layout and nonempty
source identity/digest. Duplicate Wait and Logs begin calls must be refused;
they cannot create another session. The primary-session/no-session distinction
is not directly surfaced as a public receipt field and is therefore not
claimed as a separate assertion here. Cancellation after a partial output
prefix and injected native failures are NOT_COVERED because this fixture has
no real, controllable fault source. They are not converted into simulated
passing cases.

## Fixture inputs

Set all three environment variables to actual fixture files/values before
running the spec:

| Variable | Required value |
|---|---|
| `SIMPLE_LINUX_FRESH_WORKLOAD_TEMPLATE` | Path to administrator-installed group-process-stream template SDN |
| `SIMPLE_LINUX_FRESH_WORKLOAD_REQUEST` | Path to retained Linux OCI request SDN with a real pinned image and provider CLI command |
| `SIMPLE_LINUX_FRESH_PROBE_PROVIDER` | Provider name accepted by the production decoder (`codex`, `claude`, `gemini`, or `kimi`) |

Missing input, absent installed policy/principal, unavailable runtime, request
or compiled-argv mismatch, missing actual EOF/evidence, and retained cleanup
are failures. There is no skip, fake provider, or success fallback.

## Scenario flow

1. Read bounded fixture files and decode the request, template, and provider.
2. Open the actual installed workspace root and retain its owner.
3. Select profile index zero for the exact canonical request.
4. Complete the existing bounded Create workflow and Start helper.
5. Drive the production provider CLI profiled collector through configuration,
   actual Wait, actual Logs EOF, combined evidence, and post-configuration.
6. Assert combined evidence identity and reject duplicate Wait/Logs begins.
7. Complete actual Stop, Remove, whole-cohort Absence, and settlement.
8. Close through the returned root cleanup turn.

`AUTHORED_NOT_RUN`: no compiler, spec runner, runtime, native fixture, or
provisioning command was invoked for this document/spec. The existing simple
data-only probe-progress spec is not counted as host evidence.
