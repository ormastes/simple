# Phase 2 native test runner exceeds the enforced RSS budget

Status: reproduced; native-cache scratch retention source repair pending behavioral and RSS verification.

Producer 4c479a0d3f25bcb73a9c4c8fe1735b7743c65862076c73e079b7f7bc9c607036, source f7e315569, admitted phase2 runtime capsule. Non-delegated normal/slim compiler matrix used four build threads and two test workers. Test runner build ended status 88 after 418 seconds, with no fatal MIR diagnostics. Process-tree watchdog retained status=rss-cap-exceeded, peak_rss_kib=5948320, enforced limit=5859375. Ordinary compile RSS target remains 1000000000 bytes; it is not met by this tool build.

Evidence: /mnt/wsl/simple-dbc-native-bootstrap-20261012/stage2-compiler-tests/x86_64-unknown-linux-gnu/verification/logs/test_runner_build.log and summary.env in the same verification root. First investigate serialized tool/build scheduling and retained compiler state. Keep the resource guard enforced; do not replace status 88 with a compile PASS or infer test execution from absent MIR errors. General test runtime remains unqualified.

## Native-cache identity retention candidate

The last observed completed stage was `weave_aop` (252 modules, 316406 ms),
followed by `native_cache` pending (252 modules, 316737 ms). This locates the
observed memory failure before native object workers, not inside codegen.
It does not prove which individual allocation caused the peak.

Native-cache planning calls `driver_native_shadow_witness_v1`, which calls
`native_capsule_mir_identity_v1`. Each identity builds all serialized function
JSON, length-prefixed copies and metadata rows, then joins the complete module
canonical bytes. Capsule construction/validation computes the same identity
again. No scoped scratch owner previously released these intermediate graphs;
native allocations remain registered for the build. Function JSON also appends
successive prefixes, multiplying temporary bytes for large functions.

The source candidate bounds the identity builder with the existing transient
owner used by `driver_hir_abi_interface_digest_v1`. It pauses, promotes only the
result digest and ends its scope. Borrowed MIR predates the scope and remains
owned by the caller. Canonical serialization and hashing are unchanged. Scope
acquisition/promotion/release failure is a build error; no empty identity,
resource-limit increase, cache admission waiver, or unscoped fallback is added.

The regression `native_capsule_mir_identity_scratch_spec.spl` checks exact
canonical digest bytes, digest survival across scopes and borrowed module
survival. Status: NOT_RUN. Existing nonempty capsule regressions and the real
test-runner build with its unchanged enforced RSS cap are still required.
The source candidate alone does not prove the RSS target or general runtime
qualification. No full build was launched by this repair lane.
