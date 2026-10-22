# Full-sweep API-drift lane: residuals left open (2026-10-19)

Found while fixing the fullsweep clusters (branch work/sweep-api-drift). Each is a concrete defect, not fixed there.

1. **Module-level `var g = IpcManager.new()` runs before `impl IpcManager` registers** when
   `os.kernel.ipc.ipc` is the FIRST module imported. Importing `os.kernel.scheduler.scheduler` first makes it
   work, so there is an import cycle ipc -> scheduler -> ... -> (arch/*/interrupt, abi/syscall_shim,
   riscv32/trap_runtime_v1 hold the global initializers) -> ipc. Symptom:
   `unknown static method new on class IpcManager`; reproduces with a 3-line script. Affects all of
   test/01_unit/os/kernel/ipc/* that import IpcManager first (ipc_spec, ipc_endpoint_namespace_spec,
   ipc_owned_reply_classification_spec, ...). Fix is to break the cycle or make the globals lazy; the specs are right.
2. **`std.common.structural.environment_instruction` does not exist on any ref** (checked
   origin/main, origin/release_phase3, 88aac2ffe28~1). Seven specs under
   test/01_unit/lib/common/structural/ (+ integration/system hal_environment_* specs) are requirements for an
   unlanded module (EnvOpcodeV1, env_executor_policy_v1, EnvSandboxExecutorV1, wire codec). Not an
   export dropped by mistake; the implementation has to be written.
3. **Interpreter: an imported module alias shadows a same-named local/param.** A file that
   `use std.common.sdn.value.{SdnValue}` made `value` locals in file_session_*/file_read_result resolve to the
   module namespace dict. Worked around by renaming those bindings to `item`; any other function with a local
   named after an imported module's last segment is exposed to the same thing.
4. **`*_test.spl` print-scripts** (PASS:/FAIL: lines, run with `bin/simple run`) are not runner-format. The
   runner correctly refuses to synthesise a pass for output with no summary. They need converting to
   describe/it/expect, or renaming so discovery skips them.
5. test/01_unit/compiler/mir/class_prescan_collision_spec.spl now reaches its assertions and fails
   (`expected true to equal false`) on a class/struct ownership check after prescan: real behaviour question.
6. Runner: 57 "never reported" files were not dropped by a bug. Directory discovery excludes
   `/remote/ /baremetal/ /security/ /resilience/ /fuzz/ /deploy/` by convention, silently. Fixed by printing
   an `Excluded by directory convention, NOT run` line; the sweep harness must run those dirs by name.
