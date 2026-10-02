# Resume2 HIR interface owners and implementation checklist

Status: source-only triage; one path-validator import migration proposed.
Native and behavioral specs UNRUN. No compiler fallback or contract stub added.

Evidence: `D:/dev/bootstrap-failure-catalog-20261002/windows-resume2/evidence.json`,
six HIR attempts on frozen source7734/producer2f3d. Manager checkpoint
`54c030180e920a4d297fe9380935f6ecfbc7b500` does not supply the absent owner modules
either: checked its tracked tree, not merely its sparse worktree. Consequently
PR2255 alone cannot qualify the grouped parser execution graph.

## Small existing-owner migration

`grouped_windows_main.spl` calls absent
`manager_contract.native_manager_absolute_program_v1` only to validate its
manifest path before reading it. Migrate that import/call to the existing
exported `std.common.build_manager.grouped_native_contract.native_group_absolute_path_valid_v1`.
It checks bounded text excluding NUL/LF/CR/tab, absolute POSIX or alphabetic Windows drive
paths, and rejects dot components. Existing drive tests plus new relative,
drive-relative, dot-component, and newline cases exercise the real predicate.
This removes one missing dependency only; grouped parse compilation is not fixed.

## Managed parser implementation dependencies

No equivalent types or codecs were found in the checked src trees. Do not alias
native object-build records to parser records: their artifacts/receipts differ.
Consumer source provides required calls but does not specify every field type or
wire format. Implement the following graph as one coherent parser feature:

1. `compiler.driver.driver_build.managed_parse_run_contract`: ManagedParseRunV1,
   validate/encode/decode. `grouped_run.spl` consumes run_id, source_root,
   state_root, environment, graph, schedule, profile, bindings, worker_slots,
   snapshots, worker_program/digest, broker_program/digest, keep_going,
   lifetime_ms, startup_timeout_ms, shutdown_timeout_ms, poll_ms, max_attempts.
   Bind all identities, paths, resource limits and slot/snapshot membership;
   specify canonical versioned encoding and reject malformed/duplicate records.
2. `driver_build.managed_parse_group_contract`: ManagedParseModuleV1
   (module_id/package_id/source_path/source_digest); ManagedParseSnapshotV1
   (worker/generation/snapshot digest/cache identity/max source bytes/modules;
   positional consumer at parser_qualification_evidence.spl:79 additionally
   passes a digest and target os-arch-cpu values whose exact schema must be
   recovered rather than guessed); ManagedParseActionV1
   (action/group/worker/generation/lease/snapshot/cache identities,
   package_members/keep_going). Implement snapshot digest+encode,
   action encode+basename, and module-cache key. Bind cache keys to semantic
   compiler/target/source inputs, not an arbitrary receipt string.
3. `driver_build.managed_parse_group_result` is additionally absent:
   ManagedParseModuleResultV1, ManagedParseActionResultV1, module/action codecs,
   action-result validation. Existing parent validates canonical re-encoding,
   re-reads source digests, and checks successful blob digests
   (`grouped_run.spl:97–115`); result validation must preserve exact action,
   generation, lease, snapshot and module membership, plus real failure details.
4. `action_graph.grouped_execution_adapter` is additionally absent:
   GroupedExecutionV1 and new/ready/claim/commit/recover. Compose the existing
   coordinator, artifact-service route, GroupedActionLeaseV1 and
   GroupedReapReceiptV1. Do not create a second scheduler. Parent recovery
   requires archived native reap authority before advancing generation or
   reusing previous caches (`grouped_run.spl:118–124,347,377,544,597,651`).
5. The actual parser worker is also required: `compiler.driver.managed_parse_group`
   install/action_owned APIs and `driver_build.managed_parse_qualification`
   qualification records consumed by parser_qualification_evidence/main.
   Execute real parent/worker malformed-good-malformed parsing; compare canonical
   results and exact blobs. Negative controls must reject changed sources,
   mismatched leases/generations, corrupt blobs, replayed receipts and unreaped
   workers. Source contracts without this behavior cannot close the graph.

Existing equivalents to reuse: `std.common.build_manager.codec`,
`grouped_execution_contract`, compiler coordinator/action graph/artifact bridge,
and SOSIX `group_process_owner`. The tracked consumer comments explicitly keep
scheduling and process authority in these owners. No matching managed-parser
architecture/design/plan artifact naming the missing contracts was found in the
checked frozen documentation; consumer expectations alone are not a complete
wire-protocol design. Recover an authoritative feature design if available,
otherwise write the explicit protocol/ownership design before implementation.

## Separate SIMD capability dependency

`compiler.driver.parser_simd_execution_capability_v1` is absent, but several
loader owners import ParserSimdExecutionCapabilityReceiptV1. Required APIs:
issue_verified_v1(verifier owner, live receipt, environment snapshot, feature
words, mapping authorization, affinity owner, affinity lease) and
validate_with_affinity_v1(receipt, snapshot, feature words, authorization,
affinity owner, affinity lease). See parser_structural_package_owner_v1:358–373
and parser_structural_guarded_call_v1:101–113.

Reuse live_simd_verifier_v1 and execution_domain_affinity_lease_v1; neither is a
drop-in receipt alias because callers require capability binding to mapping
authorization and exact environment/features before entering the pinned native
call window. Implement revocation/generation/source/feature/affinity mismatch
rejection and real unsupported-host controls. Do not mint always-valid receipts.
The existing four-lane status report
`doc/09_report/compiler/simple_parser_simd_gpu_jit_four_lane_status_2026-09-08.md`
already marks SIMD provider qualification incomplete; it is not this missing
capability's implementation. These two HIR attempts are missing interface-owner
dependencies, not proof of a qualified-type-name compiler defect.

## Other two HIR attempts: no proven patch

Invalid export origins: alloc_inference_analyze and PointcutKind/Pointcut are
authored in their named core modules and exported by core.__init__. The error
comes from module_import_registration.spl:360–365 when the origin owner has no
surface index. Existing lookup already has canonical alias and retained-array
fallback. Need the failing registry's owner aliases/indices and admitted source
closure to distinguish a missing surface from transport/alias corruption.

feature_registry.available: every authored reference is bound by the function
parameter (lines249–258) or immediately preceding match-result val (267/295).
Reported17:49 points to a schema constant, so the failing use cannot be located
from this receipt. Need original call/function span and local symbol registration
for available at the failure. Do not rename the variable or rewrite match forms
without proving a compiler defect. Both groups remain unresolved and unverified.
