# HIR first-profile qualification plan

All newly authored specs are NOT_RUN. They must execute with the actual admitted
native compiler/internal dispatcher and canonical V4 provider, under a bounded
outer supervisor with root's resource slot. No Rust seed or helper-only substitute.

1. Policy rejection: absent/empty closure, invalid shard, mixed modes, unknown
   options/config, loader injection and malformed policy handoff.
2. Production coordinator positive: canonical SCV/closure/policy preparation,
   retained launch pin, real ledger claims, HIR artifact and no linked output.
   Include the builder-owned cache/no-stub settings, not merely a blank environment.
3. Real pool failure: parse-valid unresolved-name fixture, two worker owners,
   fail-fast result and all_stopped barrier. Natural sibling completion is allowed;
   this case alone does not prove signal delivery.
4. Real owner cancellation/deadline: work remains failed after successful cleanup.
5. Controlled failed ticket/clock observation: authentic lease remains available
   locally for recovery; no false stopped state. These are not native fault injections.
6. Native faults still required: malformed start/ack, signal/close/reap failures,
   clock failure and owner-capacity limits through the repaired canonical boundary.
7. Measure startup, HIR completion, peak RSS, maximum live owners, output retention
   and the one shared <=5000ms retirement transaction on realistic inputs.

Implementation locations: test/01_unit/app/cli/worker_hir_profile_v1_spec.spl and
 test/02_integration/app/worker_hir_retirement_v1_spec.spl, with mirrored manuals
under doc/06_spec. The generic nested-tool broker and full bootstrap configuration
matrix remain open; initial-profile acceptance cannot substitute for those gates.
