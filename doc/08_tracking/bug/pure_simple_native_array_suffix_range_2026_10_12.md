# Native array suffix range blocks member visibility

Canonical bug: `pure_simple_native_array_suffix_range_2026_10_12`.
Bug DB reconciliation is pending; this report is not a DB update.

The retained Phase 2 native producer rejects `parts[2..]` and `parts[1..]`
in `member_layer_and_tail`. The diagnostic's colon-slice suggestion applies
to text and does not provide equivalent array semantics.

The source workaround collects precisely `[start, len)` into a typed text
array before calling the original join. It preserves both length guards,
layer selection, empty segments and Unicode. The guards establish an in-bounds
start; empty and single-component paths return before indexing. Recovery
source commit: `bb3f6ab8ab29233fcc28f1fd4c239fe86aab8bf9`.
Remove the workaround only after the actual applied native range-lowering
repair passes the original syntax and these boundary cases.

## Reviewed evidence

Packet: `build/native_probe/member-visibility-range-20261012-astra`.
Original source SHA256:
`75df5311f92a9c4a99ca452d9508560313880b4fa1f75f7fc8bee6392b1685aa`.
Applied candidate SHA256:
`6701b31d1b7fc04d7cc42861e963193b927ab9081a748d8e21bbb759e3287388`.
Actual candidate owner COFF: 11,437 bytes, SHA256
`2ae94f450302c34dbfd1b9089adba2353de09a93d776131834751bc5305f92e1`.
Requested aggregate COFF: 44,529 bytes, SHA256
`bb3e86f160e46d5fe9f61b966cdab45d5233f3ed0389f38855841fab539540de`.
Native invocation: 10.425495 seconds, peak RSS 266,828 KiB, final Job active 0.

Strict native link succeeded. The executable returned the expected sentinel
77 and printed `member_visibility_cases=18 failures=0`. Its SHA256 is
`726b89b20e0fdbe7f2e489b37c27461eaf6043b6e6c7f197ae23bff131ad8b0c`.
Cases cover both suffix starts, minimum bounds, complete tails, interior and
trailing empty segments, source-root stripping, Korean and supplementary
Unicode. The sentinel prevents a zero-return stub from satisfying the gate.
Existing successful criteria were not replayed during application.

Root reviewed the source equivalence and exact recipient/candidate hashes.
The private capsule ledger incorrectly labels evidence text fields as target
fields; those labels do not establish target admission. AMD64 COFF and native
behavior are diagnostic evidence, not complete Phase 3 compiler qualification.
No cache identity or receipt was rewritten.

The workaround retains linear suffix traversal plus join and a temporary
suffix array, but performance parity and long-running allocation behavior
have not been measured. No 0.1-second or memory-improvement claim is made.
The copied permanent native probe is a regression artifact; its repository
import path has not been qualified in a full rebuilt compiler yet.
The runner-discoverable companion is
`test/01_unit/compiler/dependency/member_visibility_array_suffix_spec.spl`:
18 scenarios with real layer and tail assertions, derived from the retained
native cases. Its runner status is UNRUN, not another native or SSpec PASS.
Background owner: the native MIR array-range lowering lane; the indexed-copy
workaround does not repair range lowering. No background implementation is
claimed by this report.

Application commit: `707a469fb59074166e5ad307423ef8421bf7e536`.
Remote landing remains subject to the user's Phase 3 buildability gate.
