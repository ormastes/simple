# Acceptance: SCV consumptive source and AST handoff

Status: proposed executable criteria; UNRUN. No placeholder SSpec or claimed
formal proof. Implements W3/W4 coverage from incremental-build metadata design.
Each criterion is executed once per admitted candidate; max3 changed-input
cycles per actual implementation feature. Closed prior features are not rerun.

## Genuine fixtures and required assertions

| ID | Scenario and real assertions |
| --- | --- |
| SH01 | Real admitted four-module diamond, two aliases of one physical file; scan then adopt. Assert actual bytes/content/digests, BFS input and bootstrap order, one compiler payload read/scan per physical file, one driver payload owner, aliases preserved and native output correct. Instrument real file owner, not a counter-only model. |
| SH02 | Exercise standalone and authenticated build-worker normal/emit_smf branches; compare ordered source identities, diagnostics, real artifacts and executable output. Nonclosure mode keeps its source-directory semantics. No fake driver or backend. |
| SH03 | Attempt sender access after move, double adoption, foreign owner/generation, stale lease, cancellation at each transfer boundary and failed destination validation. Require rejection, no inventory/artifact publication, no leaked payloads or child processes. |
| SH04 | Admit source edit changing both imported value and graph; keep old request pinned, issue new request. Old result stays tied to old revision; new output and closure reflect edit and reject old action receipt. Same timestamps must not mask byte changes. Include delete/rename/alias membership changes and forged content/inventory mismatch. |
| SH05 | Change parse-affecting aspect/capture/provider/script/advisory policy; require correct parser key and AST result. Change target/runtime/codegen-only config; preserve only genuinely reusable parser stages while native artifacts invalidate correctly. Captured root remains fixed after CWD/env changes. |
| SH06 | Cold miss then warm hit under identical immutable inputs. Compare parser AST/signatures/spans/diagnostics and native output. Record real parse invocations, transformed-byte hashing, restore work and source fetches separately. Corrupt/truncate/forge header or pool bytes: miss and real parse, never successful empty module. |
| SH07 | Syntax error in an imported body: cold and warm return the same required failure; no ready AST/object receipt. With interface-only TLDR policy, separately assert exact declared diagnostic coverage; never label skipped bodies fully checked. |
| SH08 | Interleave two captured source owners with different revisions/policies in one process; no ambient authority crossover. Then two real concurrent same-key requests through the actual shared service: exactly one producer, same authenticated artifact for waiters, bounded queue bytes and no duplicate restored mutable AST sharing. Independent service instances must not be reported as shared single-flight. |
| SH09 | Kill/cancel actual producer while waiters exist; obsolete epoch cannot publish, at most one replacement claims after lease resolution, all surviving waiters terminate without deadlock. Exercise SCC imports under bounded CPU/memory credits. |
| SH10 | Named supported TLDR import alongside unused unsupported name remains eligible; requested omitted/missing name, mixed overload, glob/global cases fall back before binding mutation. Internal canonical object dependency remains scheduled and authenticated. No header-only object availability assumption. |
| SH11 | Native transfer/GC pressure with tiny and large sources plus many aliases: byte-for-byte payload and syntax diagnostics survive. Prove scanner/global/SourceFile/vector aliases no longer retain a full duplicate heap; observe reclamation after last loan/lease and failure cleanup. Unsupported provider reports fallback, not move success. |
| SH12 | Stage observability: a deliberately bounded slow admission/read/restore produces a start marker before blocking and a terminal reason at timeout. Whole foreground includes required admission and supervision; external wrapper pins and process-only CPU scopes are separately reported. |

Tests belong in `test/01_unit/compiler/driver/` for owner transitions and
`test/02_integration/compiler/` for real CLI/worker/SCV/cache scenarios, with
generated Markdown manuals under `doc/06_spec`. Do not add tautological source
string assertions or fake CAS/source inventories. A source harness must use
the qualified canonical engine environment and audit both JIT diagnostics and
traced reads; zero traced external reads alone is insufficient.

## Performance and memory experiment

Reserve resources from fresh host RAM/disk and live-lane budgets. Use immutable
baseline/candidate executables and source/runtime/config pins, isolated caches
with explicit cold/warm state, same representative graphs and alternating
order. Choose sample count and statistical rule before launch; do not keep
rerunning green criteria. Report end-to-end foreground p50/p95, exact process
CPU versus aggregate CPU scope, peak/steady RSS and private commit, source/AST
metadata bytes, physical source reads and real parses. Include supervisor and
admission overhead separately without deleting it from user latency.

Measure cold single-SPL with imported headers and their real object dependency
closure, warm unchanged request, a large import diamond and changed-source
request. Tiny fixtures alone cannot establish memory scaling. Required invariant:
one canonical raw payload per physical source; transfer overlap no greater
than one largest source plus declared bounded metadata. AST restore/transform
heaps are separately accounted. Existing diagnostic RSS-observer-only policy
does not turn an over-budget observation into a memory PASS.

Accept a performance claim only with correctness PASS and measured improvement
outside noise, respecting independent latency/RSS budgets. Apply the optimize
skill's time/memory tradeoff rule if either regresses. Do not label cache hit
time, background-excluded time or source diagnostics as a0.1-second foreground
native result. Missing native/worker evidence remains pending.

## Proof scope

An optional bounded state model can check one-owner, at-most-one producer,
no stale publication and eventual cancellation under stated fair-scheduling
and reliable-owner assumptions. Model two revisions, two producers/readers,
bounded transport, crash and lease epochs. A checked model does not prove
runtime transport, file integrity, parser semantics or scheduler fairness;
map every transition to the implemented owner before claiming applicability.
No formal facility was run for this design.

Primitive-only progress: `source-slot-native-feasibility-20261012` qualifies
one expected native negative plus six positive provider cases across two
cycles. It does not satisfy SH01-SH12's actual driver/worker integration.
Large text may be shared (repeat count1), and short copied text may refuse free;
SH11 must carry explicit producer/ownership facts and exercise both branches.

Root owns integration and final review. Sidecars N/A. Dirty production owners
remain untouched until an exact reviewed implementation plan and native transfer
qualification are available.
