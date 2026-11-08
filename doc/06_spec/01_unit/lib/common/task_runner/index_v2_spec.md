# Mixed task-history projection V2

Status: **AWAITING_VERIFICATION** — source-authored manual; no compiler, seed,
unit suite, durable journal replay, process or container was executed.

Source: `test/01_unit/lib/common/task_runner/index_v2_spec.spl`.
Implementation: `src/lib/common/task_runner/index_v2.spl`.

The V2 adapter reads and writes the existing `task_history(identity, projection)`
PureDatabase table using the unchanged V1 sequence/escaped-row storage format.
It decodes each row through the typed V2 union, which preserves legacy native
V1 wire and accepts the separately framed common-container evidence record.
No second database, index, history table or native process surrogate is created.

Each application reads at most eight retained records, inserts one new record,
sorts those at most nine records by durable sequence and retains at most eight.
The projection retains the earliest confirmed native crash plus the newest
seven records when retaining that crash requires a slot; otherwise it retains
the newest eight. Newest-to-oldest replay uses the same bounded insertion and
retention rule. Duplicate durable sequence and duplicate group/attempt reject.
Stored projection bytes remain bounded at 131,072 and an oversized candidate
projection is rejected before mutation.
New container records additionally cap fully escaped projection-line storage
at 16,320 bytes including a conservative 32-byte sequence/tab/newline allowance.
The typed encoder enforces this before preparation or WAL publication. This
prevents an eight-record filtered snapshot group from exceeding the projection
bound even if unrelated groups separated those records in global history;
native V1 wire/admission retains its prior contract.

The journal owner calls pure `task_runner_index_prepare_v2` before committing
the WAL entry. Preparation validates, sorts and calculates the retained
projection without writing to PureDatabase. `task_runner_index_apply_v2` uses
the same calculation when storing it, so an oversized candidate cannot first
become a durable row that recovery cannot project.

| Scenario | Intended assertion |
| --- | --- |
| Existing table compatibility | Native rows written through the V1 adapter are readable through V2 in the same in-memory table. |
| Reverse replay | Twelve native rows applied newest-to-oldest retain sequences 5–12 in ascending order. |
| Earliest crash retention | Ascending and descending replay with crashes at sequences 1 and 3 retain the first crash and newest seven records. |
| Duplicate protection | Duplicate durable sequence, duplicate group/attempt and nonpositive sequence reject while existing row count remains unchanged. |
| Pure preparation | Prepared bytes equal the later stored projection; successful preparation and duplicate-sequence rejection leave existing history unchanged. |
| Existing size bound | An oversized existing projection rejects before preparing any WAL candidate and remains unchanged. |
| Corrupt projection | A projection stored under another task identity and an invalid lookup identity reject. |
| Mixed reverse replay | Twelve alternating native/container records arriving newest-first retain the newest eight in order with the correct union variants; native-only history refuses a downgrade. |
| Mixed crash retention | A confirmed native crash arriving last during newest-first mixed replay remains alongside the newest seven records. |
| Cross-variant duplicate | Native and container records cannot reuse the same group/attempt. |
| Expanded container candidate | A metadata-length-valid percent-rich container group exceeds the new escaped-line bound; both codec and pure preparation reject before publication and leave existing history unchanged. |

Mixed fixtures use the actual shared common evidence constructor and digest
helpers with synthetic provider command observations, never real container
execution claims.
The journal/snapshot owner integrates the same typed codec and adapter into the
existing `task_attempts` WAL path separately. These in-memory specifications do
not establish WAL durability, lease ownership or publication authority.

Runtime behavior, performance and coverage remain unverified. No PASS is claimed.
