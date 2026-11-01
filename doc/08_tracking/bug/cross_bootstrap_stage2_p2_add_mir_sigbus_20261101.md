# Fresh release Stage 2 crashes in MIR expression lowering during admission

Status: CLAIMED — cross-bootstrap parent, 2026-11-01.
Baseline: release/1.0.0 at 8f83c84c747.
Frozen worktree: `/tmp/simple-cross-bootstrap-20261101`.
Collector: Luna. Higher-model diagnosis planner: Astra.

## Observed result

Canonical `--full-bootstrap --stop-after-stage2` built a fresh seed/runtime,
then Stage 2: 1,561 modules compiled, zero cached, zero failed; 676.4 seconds
compile and 16.3 seconds link. The 45 MiB compiler passed its version check
but failed the p2_add frontend sanity compile. It is rejected, not admitted.

Artifact under the frozen worktree:
`build/cross-bootstrap/producer/stage2/aarch64-apple-darwin/simple.rejected`.
SHA-256: `492436748f63e804724a1f99c7409d45fe53ccd06c035cd54e226967b81aa0bc`.

MIR worker: CRASH exit -138, claimed/sealed=1, finished=false, module
`compiler.bootstrap_admission.p2_add`. The aggregate failed closed before
linking. HIR was adopted from this attempt's cache with zero reported lowering
errors; that does not prove validity or establish cache corruption as cause.

## Crash and receipt evidence

Report: `/Users/ormastes/Library/Logs/DiagnosticReports/simple-2026-11-01-163330.ips`.
Worker PID 70370. EXC_BAD_ACCESS/SIGBUS, KERN_PROTECTION_FAILURE at
`0x4e3edbb210`. Frame:
`compiler__mir___MirLoweringExpr__expr_dispatch__MirLowering.lower_expr_impl + 8228`.
Image offset 5790432; UUID `4889d149-7c9e-34dd-8456-6dbecf549206`.

Under `build/cross-bootstrap/producer/stage3/aarch64-apple-darwin`:

- `stage2-sanity.env`: fail.
- `stage2-sanity.env.frontend-bootstrap-0.status.env`: p2_add-build,
  raw status 1; Hello/module-path/MIR-retention probes not run.
- `stage2-sanity.env.frontend-failure.log`: HIR/MIR phases and worker failure.
- `attempts/attempt-20261101T072019-40892/terminal.stage2-sanity.env`.

The managed run ended, not timed out. No Hello, suite, Stage 2 admission,
Stage 3, deployment or cross-target success exists. Preserve rejected bytes,
source snapshot, compatible objects and failure receipts.

## Next diagnostic and acceptance

Instruction mapping and controlled root-cause probes are complete below.
Next, rebuild a compiler from the corrected declarations with exact producer,
source and runtime identities, then execute the tuple fixture, p2_add, Hello
and remaining admission gates. Keep diagnostics separate from qualification.

This cause is separate from the capped SimpleOS alias source-review lane.
After repair, require exact-compiler p2_add and Hello execution and all
remaining admission gates. Linking/version output cannot close this record.

## Confirmed shared return-contract error

The fresh Rust seed produced the failing executable; attributing its generated
code to the pure-Simple LLVM producer would be incorrect. Astra mapped the
faulting instruction to IfChain array length at expr_dispatch.spl:5554.
Immediately preceding tuple extractions call `rt_tuple_get` then
`rt_value_int`, boxing already-tagged aggregate handles as integers.

Commit 99a45712909 changed `rt_tuple_get<T> -> T?` to semantic `i64` and
removed the explicit type application in two wrappers. Restore the typed
contract in both MIR expression dispatch and LLVM instruction decoding.
Integer boxing and runtime pointer decoding are correct for their declared
inputs; no runtime patch or extra nil guard is justified.

Controlled native probes used exact seed SHA-256
`34d6f28f72df1253bbad9de791cc2743cbe616d01806fae4803b38a092875e19`.
The first assertion-only pair was insufficient: its red program printed PASS
despite an invalid-array-handle diagnostic. Do not count that marker as proof.
Astra disassembly nevertheless confirmed six integer-boxed tuple returns in
the old binary and zero in the typed binary.

The second observation pair differed only in extern return type and explicit
type application. Both built; the old-contract program exited 138 before
printing. The corrected program exited 0 with empty stderr and exact output:

```text
fixture=array_and_struct array_len=2 array0=7 array1=9 struct_nil=false struct_value=11
fixture=nil_optional nil_is_nil=true
fixture=scalar_pair first=23 second=29
fixture=out_of_range is_nil=true
```

Corrected source SHA-256:
`58904aab886e079b16c00adaaf6f9fce5d639b1301b94d55bf0a325935be9642`.
That exact source is retained as `test/04_smoke/bootstrap_tuple_projection.spl`.
Commands, hashes and external stdout comparisons are in the implementation
worktree's `build/cross-bootstrap/tuple-probe/observation_{i64,generic}/`.

Two diagnostic probe cycles completed, no repaired full compiler built yet.
The two production declarations/calls are now corrected locally. Refreshed
Stage 2 RTI compatibility, p2_add, Hello and normal test-runner gates remain
open. The old frozen Windows producer's RTI limitation remains historical;
this correction does not claim compatibility with that producer. Astra's
source review found zero P0/P1 issues; fresh-candidate verification is pending.
