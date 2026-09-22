# Stage2 traps when marking an already-marked MIR runtime value

Date: 2026-09-23. Baseline: `09ca68b9017f23a54f512b90b111f401d22d9cf7`.
Status: native red/green PASS; independent Astra-high review PASS.

## Cause and fix

The strict positional Stage3-route probe still fails after the separate
`remember_local_hir_type -> ()` correction. LLDB on the exact rejected
candidate identifies `MirLowering.mark_runtime_value_local+100`, reached
from `propagate_branch_collection_marks+384` and `lower_if_chain+3576`.
`is_runtime_value_local` returned 1, and the conditional branch at +32 jumps
directly to `udf #0xc11f` at +100. This is a distinct method and crash site.

The method's terminal array push causes the bootstrap producer to infer a
value-returning signature, while the already-marked path contains a bare
return. Declare the mutation-only method `-> ()`; preserve its membership
check, append behavior, and backend fail-fast trap. All 55 exact production
callers use it as a standalone mutation. No allocation, loop, scan, or I/O is
added. General implicit-return inference remains a separate open issue.

## Diagnostic authority

Worktree: `/Users/ormastes/simple-tmp/stage2-route-sigill-after-mir-return-20260923`.
Evidence: `build/native_probe/route-after-mir/`.
`reproduce.shs`, `lldb.log`, and `lldb.rss.env` retain the command, environment,
backtrace, disassembly, and sampled guard evidence. The private executable
copy matched the rejected candidate SHA-256 before and after the diagnostic:
`0fe7daf66e2e65bdd0354ce79af06d241077ad85df60d079d980f9851a9eeced`.
LLDB exits zero after recording the inferior crash; this is not admission.
Sampled process-tree peak including LLDB: 1,980,576 KiB; zero observer errors;
quiescent cleanup. The prior metadata method is absent from the failing stack.

## Production-import native regression

`test/fixtures/native/mir_runtime_value_mark_return.spl` imports the actual
`MirLowering` implementation. It checks initial absence, insertion, repeated
marking, distinct IDs, first/last-ID repeats, preserved size/order, and an
absent ID. This exercises both paths of the changed method, not a copied model.

`build-fixture.shs` records the complete native build invocation. Frozen
bootstrap-only producer SHA-256:
`3ff20095e350af7f0b5cc150fd59872b073955eced1e10f3e264ca4a1e37c0a6`.
Its runtime authority is the P0 directory
`build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-runtime-authority`.
The build uses LLVM23, `SIMPLE_NO_STUB_FALLBACK=1`, private cache/XDG paths,
Cranelift, entry closure, two workers, and the production compiler/lib source.
Every build/run uses the unchanged sampled guard of 5,859,375 KiB at 100ms,
with 180-second build and 20-second execution deadlines plus `/usr/bin/time -l`.
This is sampled enforcement, not a kernel hard limit or seed test admission.

Red: 319 modules, zero failed; prints `mir-runtime-value-first-mark-pass`, then
exits 132. Binary SHA-256:
`05abc9d2a9ac570eba6c1fb74bc1c1e4ea0cbf2a7c824f37076acb36f044b4ff`.
Build wall time 70.15s; sampled tree peak 1,130,816 KiB; max process RSS
1,048,723,456 bytes. Execution wall time 0.35s, max process RSS 9,338,880 bytes.
The build exceeds the ordinary 1 GB target; that performance limitation stays
open. Zero observer errors and quiescent cleanup on both red receipts.

Green: 319 modules, zero failed; exits zero with both
`mir-runtime-value-first-mark-pass` and `mir-runtime-value-repeat-mark-pass`.
Binary SHA-256:
`49c76712ce75160e059031f9417cebaa076f8946c124264e7948eaac86f43c93`.
Build wall time 68.78s; sampled tree peak 1,210,864 KiB; max process RSS
1,116,684,288 bytes. Execution wall time 0.35s, max process RSS 9,404,416 bytes.
The single measurements show a higher green build RSS (about 6.5% max-process)
but cannot attribute that difference to this annotation or establish a trend.
The ordinary 1 GB compilation target remains unmet. No performance improvement
or broad no-regression claim is made. Green disassembly has normal returns on
both paths and no `udf` in the changed method. Both green receipts have zero
observer errors and quiescent cleanup. Two native build cycles were used;
passing checks were not rerun.

Working direct-env audit PASS; executable spec layout count under
`doc/06_spec` is zero. There are no production environment/process additions.

Independent Astra-high review found no blocking findings in the exact source,
fixture, report, native receipts, matching binary hashes, and disassembly.
It accepted the scoped duplicate-mark fix while retaining the broader
bootstrap and performance limitations. The reviewer did not repeat green
checks. Staged direct-env audit also passed.

Full Stage2 admission, compiler tests, Stage3, broad core/MCP verification,
and publication require the parent bootstrap lane. This scoped regression
does not claim those gates have passed.
