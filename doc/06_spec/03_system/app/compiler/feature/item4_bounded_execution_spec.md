# Item 4 retained streaming execution

Requirement: ITEM4-REQ-009. **Authored manual; NOT RUN.** Canonical SPipe generation,
runtime acceptance, native execution and branch coverage remain UNRUN. Full-item
verification remains FAIL while selected implementation and evidence gates are open.

**Historical source-review finding, repaired in this integrated source:** classes have value semantics. Free-function mutations
of input selection/counters, archive traversal and retained file cursor/closed
state lack an established caller-writeback contract. The candidate and underlying
retained/spill owners require explicit returned-owner or `me` transitions before
the path or its logical quota enforcement can be claimed functional. All flows
below are authored intended behavior, not accepted execution evidence.

Follow-up source repair replaces those free mutations with `me` transitions and
named mutable owners. Writer and spill IO owners retain both file/state receivers
through failure; archive state is explicitly stored back in its array. The
provider scenario additionally checks record-budget decrement, persistent close,
second-close rejection and lookup rejection after close. Companion retained IO
methods are integrated. The correction remains UNRUN and does not clear admission.

Executable source: `test/03_system/app/compiler/feature/item4_bounded_execution_spec.spl`.

| Scenario | Real setup and action | Independent expected result |
|---|---|---|
| Mid-emission cancellation | Cancel using actual private file length after the fixed header write | Error plus the same writer cursor and file length both 288; same owners close, incomplete image discarded |
| Logical quotas | Open checked-in x64 objects with one scan record or 64 metadata bytes; link with a 4,096-byte output cap; compare scratch allowance 41,559 versus 41,560 | Named scan/metadata errors, absent rejected output, exact scratch boundary publishes 12,304 bytes |
| Direct and archive images | Link real entry/provider objects directly and through an independently encoded ordinary archive with eight-byte emission windows | Images equal; ELF64 x64 executable entry 4,198,400; four load protections R/RX/R/RW; exact size 12,304; independent absolute and PC-relative patch bytes, data and BSS |
| Publication failure | Preserve a sentinel destination while scratch admission fails and while a complete candidate collides with that destination | Named errors and unchanged sentinel; nonrecursive scratch-parent removal verifies normal-path cleanup |
| Provider selection | Retain entry object and archive provider; resolve actual `add_val` definition | Two selected objects, one archive owner, provider ownership and real symbol bytes |
| Resolution/admission failures | Missing strong provider, duplicate real providers, absent paths beyond input quota and cancelled admission | Named failure at the specified boundary; no fabricated success fixture |
| Borrowed member view | Parse the checked-in common object through a real archive member extent | Actual section/symbol values; closing view preserves archive owner; closed-view and truncated-extent errors; real archive EOF |
| Malformed archive | Truncate the independently constructed archive payload | Member bounds error through production retained traversal |

The production path is `elf_stream_link_file_v1`: retained inputs and archive
selection → scan-based layout → scalar x64 RELA window patches → private retained
image → checked spill/replay → no-replace publication. No whole object, section or
output image is materialized by this path. The test oracle may read its small
published fixture in full for independent comparison.

This is a static x64 image candidate slice, not complete bounded-engine admission.
Fixed metadata reads/header allocations coexist with configurable payload windows.
Input/serialized metadata/output/scratch/work limits are logical quotas, not RSS
enforcement. Native executable permissions, host execution, constrained worker,
no-swap policy and matched performance evidence are pending. COMMON, COMDAT, TLS,
GOT/dynamic and remaining ISA/format support remain required work; named rejection
does not satisfy their positive acceptance. Mid-emission cancellation has an
authored writer-owner scenario; execution and dedicated GNU/BSD archive-name
scenarios remain unverified. `UnsupportedBudget` stays in place.
