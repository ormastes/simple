# Private streamed ELF preparation and publication

Requirement ITEM4-REQ-009. Four executable scenarios in
`test/03_system/app/compiler/feature/item4_stream_prepare_spec.spl`.
**UNRUN**: this is a manually authored companion, not generated runtime evidence.

| Scenario | Actual observable behavior |
|---|---|
| Prepare and publish | Real x64 input objects produce private image and spill files without any destination argument. Explicit publication checks the independently expected 12304-byte ELF, entry, relocation/data/BSS bytes and compatibility with the existing one-shot wrapper. Cleanup ownership transfers and a second publication rejects. |
| Discard | Both private directories disappear; empty discard is idempotent and publication after discard rejects. |
| Failed publication | Invalid path, real no-clobber collision, cancellation triggered by actual replay-file creation, and a mutated spill payload each reject. An existing destination sentinel survives; publication cannot retry and explicit cleanup succeeds. |
| Cleanup retry | Real unrelated files block nonrecursive cleanup in both directories. Discard retains failed owners, burns publication rights, and retries cleanup independently. Successful publication remains successful with cleanup_pending and transfers exclusive cleanup responsibility to the result. Removing only the test-created blockers permits staged cleanup retries. |

Fixtures reuse `test/fixtures/linker/elf/start_x64.o` and `lib_x64.o`.
Scratch directories are uniquely created; setup failures record assertions and
return before dependent mutation. Corruption changes a real framed payload byte,
not a canned return value. Blockers are ordinary files, not injected cleanup
booleans. Output-window size is three bytes, crossing relocation widths.
The cleanup matrix also combines a real destination collision with both cleanup
blockers: failed publication retains the unconsumed, unpublished stage and image
owner before returning Err, forbids another destination, and allows discard
after the blockers are removed while preserving the original sentinel.

Future execution after independent runtime admission:
`<runtime> test test/03_system/app/compiler/feature/item4_stream_prepare_spec.spl --native-backend=llvm --sequential --no-cache --no-db --no-session-daemon --assert-ran --keep-artifacts --verbose`

This is same-process owner separation. No cross-process transfer authority,
worker qualification, no-swap, whole-job memory enforcement, five-host execution,
or performance result is claimed. Prepare-time cleanup failures still report
legacy text errors without a returned retry owner; that limitation remains open.

Pending execution follows [the item4 native execution gate](item4_linker_execution_gate.md).
This command is an unexecuted recipe, not proof that the current CLI or generated
entry is admitted. Account for all 4 declared scenarios and their actual
assertion behavior; zero reported examples or missing scenario results cannot pass.
