# Direct primary connection plan and stable binding V2

Status: **AUTHORED SOURCE-ONLY NOT_RUN**. No tests or builds were executed.
The specs use public metadata constructors and actual production helpers.
They do not fabricate native connection owners, capabilities or absence proof.

Source: `src/lib/common/contracts/container/primary_connection_v2.spl`.
Spec: `test/01_unit/lib/nogc_async_mut/container/primary_connection_plan_v2_spec.spl`.
Fixtures: `connection_plan_fixture_v2` and `connection_target_fixture_v2`.

| Authored case | Intended assertion |
|---|---|
| Canonical plan | Actual SDN bytes re-encode canonically with a newline, hash to the request digest, retain fixed stdin/signal/detach flags, and exclude the self-digest field |
| Backend and engine | Only the Windows Docker process backend with Docker runtime is admitted |
| Windows service continuity | Direct plan uses service-incarnation mode, empty boot ID and nonempty valid continuity ID; valid generic native-boot scope and populated/invalid service boot metadata refuse |
| Terminal mode | stdin and tty are admitted and produce different digests; other modes refuse |
| Resource window | Exact minimum/maximum CPU, memory and timeout values accept; negative, zero and above-cap values refuse |
| Runtime correlation | Pod, attempt, operation, generation, scope fence and parent operation must agree with the workload |
| Scope and strict pins | Invalid continuity/scope metadata and malformed lowercase 64hex pins, including the journal writer lease, refuse |
| Plan material | Valid changes to runtime/provider/installation/policy/journal lease pins, demand, identities and workload request alter the digest |
| Target-to-plan match | Exact primary metadata matches; stale request digest and valid foreign scope/runtime/binding/request/exec targets refuse |
| Attachment exclusions | Valid client and attachment-generation changes preserve the stable digest while changing the full target digest |
| Adopted and runtime fields | Every adopted identity, epoch, incarnation and runtime field remains in the stable digest |
| Scope components | Every scope component remains represented; coupled runtime fence/generation values are recomputed so targets remain valid |
| Exec namespace | Execution kind, native exec identity and exec request digest remain in the generic stable binding domain |
| Validation before exclusion | Invalid client/generation values still refuse, despite exclusion from the stable digest |

The direct Windows plan fixture uses `service-incarnation-v1`, an empty boot ID,
and nonempty service continuity. Its runtime fence derives from that actual
service scope. It does not invent a Linux boot identity for Windows.

The fixture's `journal_lease_digest` is `5` repeated 64 times. Its canonical
`journalLeaseDigest` field pins the signed actual journal writer incarnation.
The lower admission boundary must compare it with the actual retained journal's
`lease_digest`, so a fresh writer cannot reuse a plan signed for the old writer.
These pure metadata cases check strict pin validation and digest sensitivity;
they do not prove that native writer comparison or mint a journal lease.

The stable binding excludes only client ID and attachment generation. Its
generic helper can still represent valid native-boot control targets, while the
direct Windows plan refuses them. Scope mutation cases recompute runtime fence
and generation, vary service continuity independently, and vary boot/continuity
together only in an independent valid generic native-boot target.

A matching plan or digest proves metadata correlation only. These pure cases
claim no live adoption, authentication, input or geometry grant, provider effect,
host policy, native transport, or Windows qualification.
