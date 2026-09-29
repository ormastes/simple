# Admitted Stage2 minimal native compile fails at `str.clear`

Status: open runtime blocker for `compiler_minimal_native_compile_perf`.

An admitted Stage2 compiler at
`/mnt/data/worktrees/restart12-compiler_perf_a/build/restart12-build11-a-r4/output/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
with SHA-256
`68cbbbbd60ed073e2e21aac682207f0c21cef703f5fe7a920fee3e32c19af2aa`
was tried against three distinct minimal source shapes. Each bounded invocation
exited 70 in 0.01–0.04 seconds at roughly 9472–9728 KiB max RSS, emitted no
artifact, and reported `str.clear was called on a receiver that is not text`.

The failure occurs before a valid benchmark sample and therefore supplies no
baseline, optimization, or runtime PASS evidence. Source inspection localizes
the first minimal path to `HirLowering.begin_module()` clearing its diagnostic
collection before the stub-HIR boundary. Repair belongs to the bootstrap/runtime
owner, not this benchmark lane. Re-test only with a newly admitted pure-Simple
artifact and do not substitute the Rust seed.
