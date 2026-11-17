# hosted_c_target_guard_spec: stale llvm_native_link_orchestrator assertion

Status: verification-pending (filed, not fixed in this change).

At release/1.0.0 (f593c7123ca) the spec
`test/01_unit/compiler/backend/hosted_c_target_guard_spec.spl`, example
`retargets llvm-mingw clang to the Windows GNU target architecture`, fails with
`expected false to equal true` before any change from the Windows ARM64 lane.

Cause: the last assertion of that example checks that
`src/compiler/70.backend/backend/llvm_native_link_orchestrator.spl` contains the
literal text `options.opt_level, hosted_cc, entry_target)`. The call at line 378
now continues with `options.xray_thread_context_v1, options.xray_startup_consumer_v1)`,
so the source-text check is stale. The earlier assertions in the example
(including the `entry_point_c_target_args` ARM64 check) were not shown to be
at fault.

Fix direction: replace the source-text probe with a behavioural check, or update
the literal to the current call shape. Left alone deliberately so the Windows
ARM64 change stays scoped; its own coverage lives in the separate example
`plans Windows ARM64 llvm-mingw gnullvm and w64-mingw32 targets`.
