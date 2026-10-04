# Item 4 hosted ARM64 ADDEND increment

Date: 2026-10-04. Full runtime verification: **UNRUN**.

This change addresses existing ITEM4-REQ-004/006. Hosted Mach-O linking previously
rejected every ARM64 ADDEND prefix before its already-supported instruction
follower could reach the relocation engine. The shared pair decoder now serves
both static and hosted consumers. It preserves signed 24-bit payloads, consumes
the follower once, and retains named malformed-input errors. Both routes reject
simultaneous nonzero explicit and instruction-embedded addends. Imported calls
still require zero addends before selecting their generated stub.

Test intent `a1d863b52ea` and fixtures `67f0ac9b319` preceded implementation
`2a34f353063`. Independent source review found no P0/P1. Test authorship is not
an observed Simple RED/GREEN cycle. The positive fixtures came from LLVM's
assembler; signed-negative cases use guarded wire mutations because that
assembler emitted malformed negative prefixes. See fixture provenance and the
mirrored SSpec manual for the exact independent byte oracles.

Independent final review also covered the eight-scenario spec through
`ded72abf4fa`, including signed limits, static compatibility, subtractor output
and actual file-adapter destination preservation, with no P0/P1 findings.
Working/staged direct-env guards passed; the documentation tree contains zero
executable `_spec.spl` files. No full SSpec, branch coverage,
core/MCP, native Darwin execution, signing admission or five-host PASS follows
from these source checks. The default external linker selection is unchanged.

## Runtime prerequisite

The previous isolated minimal compile/run succeeded using source `9737d1217bc`
and producer SHA beginning `776ce2a1`. That diagnostic excludes this repair.
The reviewed warm runner/debugger request SHA256 is
`6e0eb8928d548d347754dcdc489fec5a47f5ad403ad114258aaf4da006fb2247`.
Its first admission at 12:56:35 UTC returned
`NOT_LAUNCHED_RESOURCE_RESERVATION_UNAVAILABLE`; no compiler/debugger was started.
This turn revalidated two live other-owner reservations and 17.70 GiB free
commit, below the helper's minimum with those reservations. Later, owner 57720
exited and its reservation disappeared. A separately identified second admission
at 13:13:37 UTC again returned null; no compiler/debugger started. The helper
returns null for either unavailable admission lock or insufficient commit, so
this second result does not identify a more specific cause. A subsequent sample
showed 17.45 GiB free commit and terminal upstream receipts; it is not an atomic
observation of the admission decision. No other owner's reservation, process or
cache was modified. Both refusal receipts and the unchanged request are retained
in the isolated diagnostic worktree; no third admission was attempted.
