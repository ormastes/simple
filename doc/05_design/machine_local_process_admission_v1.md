# Machine-local process identity and standalone admission boundary

Status: SOURCE_AUTHORED_NOT_RUN. The native runtime, platform link routes,
provider fixtures, test runner and generated-manual pipeline have not run.

The selected first identity scope is the actual current process. A private
`MachineLocalProcessPrincipalV1` contains a native owner rather than UID/SID
text. Its zero-argument factory selects Windows token observation or the Linux
installed-policy owner's verified process context. Public snapshots are data
and cannot authenticate a caller or construct another owner.

Policy membership uses exact stable identifiers `windows:S-1-...` or
`linux:uid:<decimal>`. Per-owner identity digests bind process creation,
process/thread identity, native token or UID state, namespace evidence and
generation. Legitimate separate owner generations for the same process may
differ; cross-owner comparison uses actual logical identity fields after both
owners revalidate. PID-derived digests are never durable principal identities.

Windows retains the actual primary token and private arena on the canonical
native thread. It checks TokenUser, TokenStatistics TokenId/AuthenticationId/
ModifiedId, creation FILETIME and strict kernel boot-environment namespace on
every use, and refuses any impersonation token unless OpenThreadToken reports
exact ERROR_NO_TOKEN. It never changes or reverts production security context.
The native NT boot-environment ABI remains unqualified; a counter fallback is
excluded and boot-identifier equality alone is no native continuity proof.

Linux uses one dedicated administrator-delegated service UID and rootless
Podman. The native policy/context leaf verifies real/effective UID equality,
initial UID/GID mapping, genuine procfs/nsfs observations, process/thread start
identity and retained namespace/path provenance. The Container authority
decodes the protected selected engine policy and compares expected_uid with
that actual service UID. No root daemon, multi-UID broker, installer, automatic
elevation or second namespace-observation implementation is introduced.

The neutral storage owner selects only library-owned fixed OS roots. The
authority retains the exact policy digest, actual provider binding and shared
writer; no caller selects a root or store. The standalone opener rejects
managed mode before provider observation, checks native process membership,
then transfers reader and principal obligations together into storage cleanup.
Writer-close uncertainty retains the principal. Close reports consumed Linux
descriptor errors distinctly and never releases a durable resource charge.
Private canonical pair progress is keyed by id/generation and actual process/
native-thread identity. Confirmed-consumed components are cleared from future
close work; only a live partner can be retried. The first diagnostic survives
retained partner cleanup and remains available after the final consumed-error
result. Copied aliases share the same progress. The native lower contracts stay
unchanged; the pure production transition has explicit modeled regressions,
which are not evidence that a native close fault was executed.
The genuine Linux procfs origin latch or Windows canonical native guard runs
before any pair-registry access or closed-status report. Matching numeric PID/
TID cannot establish fork origin. Generic stale and unknown close strings never
clear a component; only positive consumption or this pair's prior closed record
permits skipping native cleanup.

Actual process admission checks both the retained factory principal and the
provided genuine owner, canonical local request metadata and resource ceilings.
Fresh WAL refuses until a genuine migration fence establishes legacy-writer
exclusion and adoption safety. Unknown retained history also refuses. The
previous managed missing-fence guard and exact charged recovery remain intact.
No forged distributed grant, positive local claim, competing journal, marker
file or caller boolean supplies missing capacity authority.

Work remaining before actual workload use: a kernel-authenticated service peer
owner for daemon clients, genuine migration/adoption evidence, bounded durable
standalone reservation transitions, provider-backed termination/absence proof,
settlement/release, guest profile and mount resolution, and common Container
execution/terminal ownership integration. Production Caret remains unchanged.

Authored system manuals describe the current Windows identity and direct local
admission-refusal fixtures. Their assertions remain NOT_RUN; source review
does not qualify native behavior or complete the Orchestrator feature.
