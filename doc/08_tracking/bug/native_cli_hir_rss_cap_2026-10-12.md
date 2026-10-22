# Full native CLI compilation exceeds the RSS cap in HIR

Status: FAIL, terminal producer-bound matrix evidence.

Producer: c27cb117978d2212cae16a6d956690e13003435f73f2047f1fa237f2fa8a8466; frozen source: 6ec114562. Normal/slim, Cranelift, non-delegated compiler matrix; three build threads, one test worker. CLI build failed status88 after793 seconds, max_rss_kib=5882956, against the unchanged5859375 KiB cap. No qualified CLI artifact was published. Its last build progress was HIR 342/2534 modules at711807 ms (compiler.driver.driver_source_loading), not native-cache planning.

Logs: /mnt/wsl/simple-dbc-native-bootstrap-20261012/stage2-compiler-tests/x86_64-unknown-linux-gnu/verification/logs/compiler_cli_build.log. Summary: corresponding verification/summary.env, expected/actual producer digest c27cb117…; rejection: stage2-compiler-tests/x86_64-unknown-linux-gnu/rejection.env. Bootstrap terminal verdict: ABORTED at stage2-compiler-tests, exit1, signalnone.

The nested owner repair allowed CLI compilation past the old facade collision, but the full tool remains unqualified. This observation is not comparable to the old14-second collision failure as a performance baseline. It occurs before MIR identity serialization, so it does not verify that scratch repair's RSS effect. Independently, the test-runner build failed status1 after373 seconds, max_rss_kib=2946784, on the multiple-wildcard MIR error. The captured-record callback also failed exact runtime output.

## Linux release_phase3 confirmation (2026-10-16)

Three bounded Stage 2 repair/verification cycles on x86_64 Linux reproduced the
same terminal full-CLI boundary under the canonical normal/slim matrix. The
final admitted Stage 2 producer was
`850bfd1fff057800773a52d9459bc09a3412477b6a7dd3b1eedd5c85b1e1c193`.
Its CLI build completed 2142/2678 HIR modules with zero compiler failures, then
exited 137 at `backend_vulkan_glass_material_spirv`; GNU time recorded
5820664 KiB maximum RSS against the 5859375 KiB enforced tree cap. No CLI
artifact was published. The preceding cycle ended at the identical module with
5790888 KiB maximum RSS. This is deterministic x86 HIR retention evidence, not
a source diagnostic or an admitted memory repair.

Do not raise the RSS cap, disable the guard, substitute the Rust seed for tooling, resume Stage3 from this rejected output, or label compile-only sanity as Phase3 PASS. No further full bootstrap or exhausted callback retry was started. Future repair work must use a fresh bounded scope and retain these exact failures; authoritative source/producer/runtime bindings and immutable caches remain required.
