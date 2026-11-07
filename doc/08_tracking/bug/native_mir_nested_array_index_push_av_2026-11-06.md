# native_mir_nested_array_index_push_av_2026-11-06

- Severity: P1, status: fix-implemented-verification-pending
- Found while splitting the repro for mutate_through_index_loses_write_2026-07-31.

## Repro
`test/fixtures/compiler/mutate_index_nested_array_push/main.spl`:

```
var grid: [[i64]] = [[], []]
grid[1].push(7)
```

The native build uses `s3_fable46_w5` (a copy of `C:/dev/p3new/s3new/s3_fable46.exe`) with the `s3sanity/run_case.ps1` recipe at CapGB 4. The compiler exits with rc=-1073741819 (0xC0000005) at `mir_lower:first_module`, and no objects are emitted. The interpreter (`bin/simple.exe run`) passes.

## Repaired owner; native qualification pending
The mutating-method write-back pre-lowering for an `Index` receiver whose element type is itself an array is in `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` (wb_kind 1, ~line 4369).

## 2026-11-06 diagnostic producer qualification (01a1afac/index-push)

The original crash remained OPEN during these attempts. No lowering repair or current-source crash
reproduction is claimed by this lane. Source was frozen at
`bdc3b07f6546204f39d0c79db07922455603fc6f` in the isolated
`C:/dev/wt/mir-index-push-d88f` worktree, branch `work/mir-index-push-d88f`.

The attempted producer is an immutable copy of the provisional, mixed-generation
self-hosted `s3_fable50_laneB.exe`, SHA256
`5B00D3D5CE63ABE17D9F9CB5A475C4309201DC36B8BD520EF53AF93D8B3C9DB5`.
It is not an admitted compiler. Before attempting the dependent P1 fixture,
the lane required this producer to compile, link and run the existing
`examples/01_getting_started/hello_native.spl`.

Three bounded Hello attempts used the LLVM backend, target
`x86_64-pc-windows-gnu`, `core-c-bootstrap`, a private cache, and an 8 GiB /
1800-second process-tree guard. No Rust-seed fallback was used.

- Attempt 1: exit 1 after 15.0 seconds, zero objects. The Hello entry was absent
  from the sparse checkout after a rejected sparse-checkout CLI option;
  admission reported `source-inventory-scope-unsupported`. The existing entry
  was then populated without changing its contents.
- Attempt 2: exit 1 after 742.6 seconds, peak tree RSS 1.98 GiB, one SPL object.
  HIR/MIR/LLVM completed; runtime C compilation failed because the sparse
  checkout omitted `tools/counterpart/sdk/c/simple_counterpart_abi.h`.
- Attempt 3: the required counterpart SDK was populated and the same native
  cache was reused. Exit 1 after 200.0 seconds, peak tree RSS 1.07 GiB, one SPL
  object. Runtime C compilation completed, but the generated GNU link command
  omitted `-lwinhttp` and failed on WinHTTP imports, including `WinHttpOpen`,
  `WinHttpConnect`, `WinHttpQueryHeaders`, and `WinHttpReadData`.

No Hello executable was produced or executed. Consequently the original P1
fixture was not run, no acceptance criterion passed, and no compiler source
was changed. These prerequisite failures do not diagnose the array-push crash.
The three new attempts plus the original reported failure consume four of the
six permitted attempts; two remain. Do not restart unchanged qualification.

Retained local evidence is under
`C:/dev/simple/.git/worktrees/mir-index-push-d88f/evidence/`: immutable producer,
`producer-hello[-v2|-v3]-build.log` and `.err`/`.cap` logs, and the exact failed
GNU link response file
`producer-hello-v3.exe.simple-native-build-97784-1793953298116219.tmp.link.rsp`.
The native-build invocation used `--entry-closure --entry
examples/01_getting_started/hello_native.spl --source src/compiler --source
src/lib --source src/app --runtime-bundle core-c-bootstrap --target
x86_64-pc-windows-gnu --backend llvm --cache-dir <private> --output <private>`.
Only attempt 2 additionally requested `--refresh-source-authority`.

Next action: obtain a qualified producer/runtime link, retain its exact pins,
then execute the original nested-array fixture before changing its suspected
owner. The broad compiler/lib/MCP/LSP checks and PR admission remain UNRUN.

## Independent owner regression, 2026-11-06 (01a1afac/index-push)

Source commit `83c17508b4a90ca1e89c574bef26e3b663d33bbd`, landed on
`release/1.0.0` by PR #7267 (merge `92bbd1fd453`), replaces the optional
`emit_call`/`if val` transport with `emit_call_value`. The loaded receiver is
then recorded directly as a runtime value and receives its element provenance.
The landed change identifies the native Option-box-versus-LocalId payload
transport as the cause. It adds empty integer, text, untyped and pop language
regressions to `mutate_through_index_writeback_spec.spl`.

After refreshing the release ref, the independent lane found this repair
already landed and retained it rather than duplicating the implementation.
Its worktree was advanced to `bbfe33dd9f1d1c0007f79788b5f8ff67b2fddbd0`
before authoring
`test/01_unit/compiler/50.mir/nested_array_index_push_local_identity_spec.spl`.

The two compiled-only cases parse the original empty integer-array shape and
its text-array sibling, lower real HIR through the actual `MirLowering` owner,
and inspect generated MIR rather than compiler source text. They require one
target function and one indexed getter, a declared LocalId for every call
operand, and the getter's exact result local as both the push receiver and the
value written back to the same base/index. A transported Option-box identity
cannot satisfy these connections (and the original native crash also fails the
case). This is a regression contract, not an observed pre-fix red/post-fix green
claim: the cases are authored and UNRUN while producer qualification is blocked.

No further behavior attempt was started, so the cumulative attempt count stays
four of six. Compiler source is unchanged in this independent lane. Native
execution of this owner regression and the original fixture is still required;
an interpreter-only run must not be used to close the native transport defect.
