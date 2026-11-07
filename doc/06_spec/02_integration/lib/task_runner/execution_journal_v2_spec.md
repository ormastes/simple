# Same-WAL execution journal and snapshot V2 integration

Status: **AWAITING_VERIFICATION** — source-authored manual. No compiler, seed,
integration suite, journal I/O, native task or container was executed during
authoring. The assertions below describe executable test source, not recorded
results or coverage.

Source: `test/02_integration/lib/task_runner/execution_journal_v2_spec.spl`.
Owners: `src/lib/common/task_runner/journal.spl`, `index_v2.spl`,
`execution_identity_v2.spl`, and `snapshot.spl`.

When executed, these specifications create real secure temporary directories,
open the actual PureDatabase task-journal owner with its OS lease/lock, register
semantic task metadata and publish through the actual segmented database WAL.
They use no mock journal, fabricated commit, fake revision or substitute index.
Attempt identity digests are computed from the registered metadata before
either native or container rows are appended. Shared process/container values
remain synthetic codec fixtures; their presence in the WAL does not claim that
a process, container wait, absence query or signed parent acceptance occurred.

| Scenario | Intended assertion |
| --- | --- |
| Mixed publication and reopen | Native V1 append followed by Container V2 append for the same registered identity publishes both through `task_attempts` in the same WAL. Native PID remains 41; container attempt, execution plan, runtime and absence identity all preserve attempt 3. Release/reopen returns the exact committed revision and both typed records; native-only history rejects the container downgrade. |
| Physical WAL representation | The real committed chain is read through strict revision/segment APIs. Its two attempt payloads decode as container then native when traversed newest-first. Only the existing inventory/completion/attempt tables appear. |
| Snapshot execution window | A selected group with native attempt 1 and container attempt 3 remains recoverable in the V2 window after ten newer unrelated native runs displace it from global newest-eight history. Native-only window history rejects the container; the global native-only projection still reads normally. |
| Publication protection | Re-appending the same container group/attempt, using native-only append to downgrade a mixed history, and submitting an oversized escaped container line all reject. The actual WAL current revision and stored history remain unchanged. |
| Missing inventory | With two registered identities, a container-only completion removes exactly its identity from missing inventory; completing the native identity clears the remainder. Release/reopen preserves the container-only typed history and zero missing rows. |
| Filtered-window size | Eight individually bounded container rows with a percent-rich group are interleaved with unrelated native rows. Snapshot group filtering reconstructs all eight container attempts in order while global history remains bounded at eight. This covers the case where the filtered rows never coexisted in the global projection. |

The per-container outer escaped-line bound is enforced before WAL publication,
so valid newly introduced container rows cannot form an oversized filtered
eight-row window. Legacy native V1 process identity and wire contracts remain
unchanged. Pure index preparation precedes the same authoritative publication
path and does not create another history store.

Temporary directories are removed only after explicit lease release in normal
successful test completion. No release, qualification or publication PASS is
asserted until the permitted runtime executes these integration specifications.
