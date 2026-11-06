# MIR/codegen repair campaign — release/1.0.0

Status: in progress; no new native PASS claimed.

The user requested all MIR/codegen bugs be fixed, alongside the ongoing node
attribute implementation, and authorized a twelve-hour continuation beginning
2026-11-06 19:59 UTC. This inventory is finite and evidence-based; it does not
claim all compiler defects are known. Preserve existing source workarounds until
the affected native paths pass with a source-matched producer.

| Cause | Current evidence | Required next result |
|---|---|---|
| Nested indexed-array push AV | Existing repair `83c17508b4a` writes the call result directly into the receiver; native replay pending | Compile/run `test/fixtures/compiler/mutate_index_nested_array_push/main.spl`, including selected and sibling row checks |
| Generic method Result Ok provenance | Existing repair `5b98de2126c`; prior seed evidence is not native admission | Execute `result_payload_provenance_spec.spl` with no MIR errors and native generic-method replay |
| Result Err binder provenance | Historical Stage 2 failure 5/5; existing unit shape did not reproduce it | Compile/run `native_result_err_generic_method_payload.spl` without a typed alias, then replay actual simple_ring closure |
| Optional trait field assignment | Historical admitted Windows producer rejects trait-to-trait field copy as missing concrete implementation | Recover declared field type without reboxing the trait object; test Some, None, distinct implementation identity, and incompatible owners |
| Trait call through optional field | `self.bitmap!.reducer` declaration recovery stops at Unwrap | Preserve declared type through unwrap and use exact trait dispatch; execute native fixture and DB closure |
| MIR registry lifetime | Stored-value journaling repair exists; older by-value journal probe failed | Source-matched registry regression and self-build; do not duplicate existing source fix |
| Native struct receiver projections | Existing source workarounds/repairs; latest native qualification incomplete | Run receiver smoke fixtures with refreshed producer; keep historical failures distinct from current ones |
| Windows pre-link diagnostics | AVX loadgen report says error text lost before linker launch | Independently identify/report the linker error; this is not established as a MIR defect |

Relevant reports remain under `doc/08_tracking/bug/`; ownership is tracked by
the existing bug-claim tool. Parallel lanes own distinct source files or explicit
helper regions. No unrelated dirty changes or foreign bootstrap processes are
part of the repair.

## Execution boundary

The separate frozen bootstrap remains at
`6e03930143983a5c9861321f67aff300b07f16ed`. Attempt 6 linked a candidate but failed
frontend sanity because 9,121 MiB headroom was below the default 24,576 MiB
reserve. It is rejected, not an admitted feature-test runner. Attempt 7 reuses
compatible caches with one worker, enforced RSS limits and an explicit 4 GiB
reserve. All normal admission gates remain required. Its log is
`D:/dev/simple-node-attribute-bootstrap-20261106/build/node-attributes-qualification/bootstrap-attempt7.log`.

The independent boot2 build reported 555 failures after a 300-second
`driver_aot_pipeline.spl` timeout: one executed failure and 554 unattempted rows.
This is neither 555 MIR defects nor evidence that those rows pass.

Native fixture success from an older admitted producer diagnoses that producer;
it does not qualify newly edited compiler source. Final acceptance requires
rebuilding the affected producer, executing regressions and applicable core/MCP
checks, reviewing the exact PR diff and comments, and merging to release/1.0.0.

Attempt 7 terminated with exit 1 after reusing 1,592 native modules and rebuilding
two. Sanity rejected the default per-file pool: two 9,000,000 kB workers require
30,000,000 kB free, while the observed headroom was about 4.2 GiB. The outer
`--jobs=1` does not select that inner route. Attempt 8 explicitly selects the
supported `SIMPLE_FILE_WORKERS=0` route, preserving the 4 GiB reserve, RSS
enforcement and all admission checks. Its log is `bootstrap-attempt8.log` in the
same qualification directory; attempt-7 sanity receipts were preserved first.
This is a resource-route change, not a MIR fix or a successful test result.
