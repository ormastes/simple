# Native process capture consumes its result block

Source: `test/01_unit/lib/nogc_sync_mut/process_capture_owned_result_spec.spl`.
This is a manually reviewed companion to the executable specification; no
doc-generation or test-execution result is inferred from its existence.

**Status: awaiting-verification. All five compiled SSpec cases are UNRUN.**
They require an admitted, source-matched P2 compiled runner. Follow the native
test workflow in `doc/07_guide/infra/testing/native_test_binary_workflow.md`;
Rust runtime-only tests and a P1 fixture are separate diagnostic evidence.
Execution remains subject to the original lane's exhausted six-cycle budget
and root's explicit diagnostic/resource authorization.

The specification calls the production `process_capture_result` consumer with
actual allocated three-word blocks or an actual process provider. It does not
replace the consumer or manufacture successful process output. The block's
third word is an untagged signed exit status; empty streams may use runtime NIL.

| Scenario | Setup and action | Required assertions |
| --- | --- | --- |
| Null result | Pass the provider's null allocation-refusal sentinel directly to the consumer. | Empty stdout; error text `native process capture returned no result`; status minus one. This case does not force a real allocator failure. |
| NIL streams and signed status | Allocate 24 bytes and write runtime NIL into both output slots, with raw status minus seven; call the real consumer. | Empty stdout and stderr; status remains minus seven. |
| Invalid stream handle | For each stream position, allocate a block with minus one in that slot and NIL in the other; call the consumer. | Empty stdout; error text `native process capture returned invalid text`; status minus one for either invalid position. |
| Both real child streams | Launch `/bin/sh` on POSIX or `cmd.exe` on Windows, producing distinct stdout/stderr markers and exit seven; consume the returned block. | Positive block pointer; both markers retained; raw status seven; both copied strings remain readable afterward. |
| Real empty output | Launch a successful child that writes neither stream; consume its actual provider block. | Positive block pointer; both outputs empty; status zero. |

Allocation-dependent cases first assert a positive block pointer. The guarded
consumer call after that assertion prevents a null dereference; it does not
turn allocation failure into a pass. All expected strings and statuses are
checked through the built-in matchers in the executable source.

These five cases verify consumer behavior and payload copying. They do not
independently establish that the raw block was removed from its allocation
registry. That lifecycle proof belongs to a composition-correct standalone
probe, with exact producer and linked-runtime provenance.

The historical `test/fixtures/compiler/process_capture_owned_block/main.spl`
diagnostic built and linked but FAILED exit14. Its actual saved word count was
not printed and its linked runtime remains UNKNOWN. A raw-only scope is not
the canonical C registry's scope, so attribution remains conditional. The
separate canonical-scope fixture in PR7547 uses the established transient
wrappers and reports actual observations; its native execution is also UNRUN.

The three reported Rust owner-test passes from attempts3/4 remain narrow
runtime-only diagnostics. Neither those results nor source-only PR landing
qualifies Windows native-all, the Simple consumer, P2/SSpec, the full test suite,
or compiler/core/MCP readiness. See
`doc/08_tracking/bug/nativeall_process_capture_tuple_provider_missing_2026_11_06.md`
for the preserved attempt ledger and exact evidence hashes. The bug is not
marked fixed until the outstanding qualification is completed.
