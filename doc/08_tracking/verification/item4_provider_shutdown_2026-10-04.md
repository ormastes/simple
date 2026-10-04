# Provider terminal shutdown verification

STATUS: FAIL — full item4 and Phase 4 are not ready.

Source scope: strict allocation-free active generation retirement; terminal,
idempotent lifecycle shutdown; busy refusal before mutation; sticky closing;
tracked generation cleanup and retained failed owners for retry. New admission,
dispatch and recovery are refused once closing starts. Operational recovery
remains separate from terminal cleanup.

Tests were committed before implementation: four generic retirement scenarios
and two actual mapped-provider shutdown scenarios. The latter require a real
hosted image and exit 42 before shutdown. Busy flags are explicitly injected
state-machine preconditions, not evidence of concurrent execution. No synthetic
unload success or failure stands in for a real mapping operation.

Independent source review covered core and acceptance commits with no P0/P1
finding. Root reviewed generation identity, pin lifetime, slot reuse, cleanup
writeback and post-close guards. This is source evidence only.

Native Simple compilation, scenario execution, canonical docgen, branch coverage,
core/lib/MCP checks, native smoke and NFR measurements: UNRUN. The known runtime
candidate remains unadmitted; no further diagnostic build or seed fallback was
attempted. Authored manuals are not generated execution evidence.

Remaining per-item implementation/test obligations are preserved in
`doc/03_plan/compiler/linker/item4_verification_readiness.md`. Real unload-failure
retry execution, production CLI routing, trusted manifest activation, required
operation binding/sealing, bounded resource enforcement, complete Mach-O/RISC-V
semantics and the platform/product corpus remain open. No full completion,
Phase 4 admission, release tag or publication is claimed.
