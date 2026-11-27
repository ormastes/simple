# Final mono repository root outside its issuance scope

Status: focused production issuance and consumption verified; downstream MIR failure remains.

The repaired VmFlags focused build parsed and lowered all 21 HIR modules, then
all three ledger-backed MIR workers reported zero generic templates and failed
with `mono final ownership failed` before MIR claims. Evidence:
`/tmp/simple-vmflags-repaired-hir-20261029/attempt/vmm/build.log`.
This is an ownership boundary failure, not evidence that kernel objects are
unsupported. Two bounded debugger probes did not capture the actual failing
ownership flags; the second reached the real ledger worker but expired.

The final issuance factory constructed `MonoArchiveFinalRepositoryV1` before
starting its transient scope, then assigned scope-owned fields and promoted the
root. A representative 17-field native probe using the real transient APIs
returned ownership failure for both inferred and explicit generic promotion.
Moving only scope creation before the root constructor made both variants pass,
including retained nested array and dictionary content after scope closure.
This disproves explicit generic specialization alone as a repair for that probe.
It does not exercise the production issuance factory or prove its failing flag.

Baseline receipt: `/tmp/simple-mono-promotion-seed-probe-20261029/run.log`
(`inferred=3 explicit=3`, exit 1). Changed receipt:
`/tmp/simple-mono-promotion-seed-probe2-20261029/result.sdn` and `run.log`
(`inferred=0 explicit=0`, exit 0), artifact SHA256
`75f92bedda83d78ec33ab0bb07f38e7748b64fedfdefcbc667021734fa8c3982`.
Both were isolated bootstrap diagnostics produced by the admitted Rust seed
SHA256 `f4af78b7f903d564cd1980cb4d171451a65d3ef4a31292ca06e7b6275c7358ef`,
with source/tool/runtime hashes recorded in each output directory. These are
bootstrap-path results, not pure-Simple producer parity qualification.

The candidate moves the existing scope-begin check before the production root
constructor. It preserves all ownership checks, serial behavior, scope closure,
and post-close error returns. There are no explicit early returns between the
successful begin and existing pause/promote/close sequence. The checked-in probe
retains the successful in-scope contract; the failing baseline remains evidence.
The rebuilt compiler evidence below supports incremental landing of this narrow repair; it does not qualify the complete build.


## Rebuilt pure-Simple production evidence

The attempt 6 admitted producer SHA256
`72b21f6a771c5df38094af04863f9354328d8f95de0406dec641ac08e733a06d`
ran the original focused VMM source-root/entry-closure route with phase logging.
Source inventory SHA256 was
`88d9a448e1c488b44f8831e525994b30b4f021df97dc7bbac45e307ea81894c7`;
source, runtime and tool immutability checks passed.
Evidence: `/tmp/simple-release-1.0.0-phase2-attempt6-vmm-mono-evidence-20261029/attempt/vmm/build.log`,
SHA256 `cd59f60986cb43e68b85a3b030e6ba9410d0338cba2da65b4d68d0e0c97a2f6f`.

Three initial workers entered `carrier=owned-archives`, completed phase 4,
and subsequently failed with
`MIR complete declaration projection failed: MIR declaration repository integrity failed`.
The stdout/stderr twins duplicate each phase/error marker; they are not additional
workers. The original `mono final ownership failed` did not recur.

This downstream location is substantive consumption evidence: the declaration
factory first checks the final repository's private pin, context, rows, digest
and stored blob. Every ordered module then passes final-repository revalidation,
body identity/digest checks, declaration projection, result/diagnostic promotion
and scope closure before reaching the new declaration repository seal.
Independent Astra review found no P0/P1/P2 issues in the narrow relocation and
confirmed that these checks separate issuance consumption from the later seal.

The new MIR declaration repository is itself constructed before its seal scope.
That is a plausible repeat ownership defect, but its combined error tests
validity, pause, promotion and scope end; the failing predicate is not known.
No fix for that second boundary is included. The coordinator selected one unsharded fallback after all three failed workers
finished with zero claims; this was not a replacement generation. The external
300-second watchdog ended collection with
exit 124, peak RSS 4,606,188 KiB and `quiescent=1`. No object was published or
executed. This is not a successful full VMM compilation, CLI build, runner build,
or release qualification; those failures remain explicit.
