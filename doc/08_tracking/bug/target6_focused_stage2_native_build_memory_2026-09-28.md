# Target 6 focused Stage2 native build reaches about 40 GiB RSS

Status: OPEN (2026-09-28). This blocks native qualification of the V2
package-index action digest and the wider Target 6 performance cohort.

The admitted pure-Simple Stage2 compiler binary has SHA-256
`d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`.
From the isolated Target 5/6 worktree, a focused no-stub probe invocation
with `native-build --source src/compiler --source src/lib --entry
test/fixtures/compiler/package_index_publish_cas_native_probe.spl --output
build/mini_builds/target56_index_v2_cas_final_probe` reached about 40 GiB RSS
and timed out at 180 seconds. A retry after simplifying the V2 action-digest
expression also reached about 40 GiB and timed out at 120 seconds. The logs
are `build/mini_builds/target56_index_v2_final_native_build.log` and
`build/mini_builds/target56_index_v2_simplified_native_build.log`.

An earlier V2 probe built 28 units and passed before the final action-digest
and empty-graph-route edits; that proof does not cover the final source.
The observed high memory may come from broad source-root scanning, codegen
specialization, or host contention. There was no compiler diagnostic or
assertion failure before either timeout, so the cause is still unassigned.

Next isolate the exact source closure and compare bounded builds with and
without the final V2 action-digest edit using the same compiler binary and
cache policy. Record wall time and max RSS. Fix the compiler or probe setup
before claiming a Target 6 native PASS; do not replace it with a Rust-seed
result or a narrow interpreter-only check.
