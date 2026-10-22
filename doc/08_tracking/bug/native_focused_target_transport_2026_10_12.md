# Focused bootstrap target transport

Bug: `native_focused_target_transport_2026_10_12`.
Canonical bug DB reconciliation is pending; this report does not represent a DB update.

## Failure and ownership

The focused native-build CLI captures `--target` in `SIMPLE_NATIVE_BUILD_TARGET`.
`src/compiler/80.driver/bootstrap_api_fixed.spl` initializes default compile
options without copying that target. The driver then receives an empty target,
so explicit target identity is lost before capsule and backend selection.
This is a supported compiler defect, not an unsupported-host feature.

Capture the target once at this bootstrap API boundary through the existing
`std.nogc_sync_mut.io.env_ops.env_get` facade. Preserve empty-target host
fallback and the separate CPU configuration. Keep the existing options
initialization in place to avoid an additional aggregate-return boundary.

## Evidence and limits

The private source factory probe reproduced missing-target RED (exit 13) and
GREEN (exit 0). Six witnesses cover CLI target and normalization, equals
spelling, capture stability, inherited target, empty host fallback, and CPU
environment preservation. Both runs ended with zero active Job children,
unchanged inputs, and 24 confined source reads.

Evidence: `build/native_probe/mir-json-perf-review-20261012-astra/native-target-propagation/SOURCE_TDD_EVIDENCE.json`.
Result SHA-256: `2da10096d5a416890771acb8da46e049394071003fb006e9a8d7bd363779df9a`.
The probe used a factory extraction and hybrid interpreter demotion. It does
not prove the patched full API, native aggregate copies, deployed producer,
object architecture, capsule identity, or a performance improvement.

The bootstrap-direct route separately passes an empty target to capsule
freezing and native compilation even though its linker uses the context
target. That owner is dirty in the shared worktree; its private proposal is
unverified and must not be folded into this repair.

## Remaining acceptance

After an affected producer rebuild, verify explicit target transport through
the actual API to emitted capsule and object architecture, empty-target host
behavior, CPU identity, and target-change cache invalidation. Cover both
ordinary and bootstrap-direct routes. Preserve other sessions' dirty files
and existing build caches; do not promote incomplete target metadata.

Local source repair is applied as a direct assignment after the existing
options initializer, with no additional factory or aggregate-return boundary.
Astra's minimal direct proposal independently matches those executable
statements: `TARGET_DIRECT.patch` SHA-256
`ba3f3f40d8b3b62ed195dafb720a3089a26f1bfdbc5c9d83542a40d5a3757d71`.
Its evidence explicitly limits qualification to extracted real-options
initialization and assignment, not the full API/native driver. The explanatory
comment in the shared repair is additional; executable statements agree.

The existing live producers are unchanged. Native qualification, deployed
performance evidence, and remote landing remain pending.
