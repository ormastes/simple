# Positive mapped-provider acceptance

Authored companion; execution and canonical docgen UNRUN. Requirements:
ITEM4-REQ-002, ITEM4-REQ-006, ITEM4-REQ-007 and ITEM4-REQ-010.

Prerequisites fail explicitly: admitted native SSpec runtime, built V2 provider
at `build/providers/item4-linker.so`, Linux x86-64 GNU host, PIE CRT/libc and
dynamic loader, `SIMPLE_LINKER=internal`, and the checked-in hosted main object.
Explicit native configuration disables cc fallback and selects no Simple runtime.

| Scenario | Actual operation and independent check |
|---|---|
| First mapped provider | Link main, inspect ELF64 PIE/load bounds/entry/interpreter, execute and require exit 42 |
| Repeated pinned generation | Link twice to unique outputs and compare complete bytes |
| Replacement with old pin | Old and new sessions both construct and execute valid matching images |
| Retired mapping collection | Refuse collection while pinned, release and collect, reject stale session, link through replacement |
| Rejected replacement | Wrong artifact digest cannot change active generation; old session still links and executes |
| Exhausted tables | Real mapped link succeeds, new generation/session fail, independent static recovery still links and executes |

Receipts require Success, actual `internal:elf`, matching Linux x64 target and
NotCertified accounting. Cleanup releases retained sessions before collection,
publishes static recovery before collecting the final mapped generation, and
removes only outputs in the fixture's unique temporary directory.

This tests provider APIs. Production CLI selection, registered composition/seal,
immutable dependency closure, resource enforcement, latency/RSS and full native
corpus qualification remain open. No source review marks any execution gate PASS.

After runtime admission: `test test/03_system/app/compiler/feature/item4_linker_pack_positive_spec.spl --native`;
then `spipe-docgen test/03_system/app/compiler/feature/item4_linker_pack_positive_spec.spl --output doc/06_spec --no-index`, requiring zero stubs.
