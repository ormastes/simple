# Idle MIR workers incorrectly enter native emission

Status: corrected-producer focused regression PASS; overall bootstrap qualification remains incomplete.

Canonical evidence: `/tmp/simple-release-1.0.0-phase2-combined-build-attempt5-20261029/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/module-diagnostics/attempt.uH8OJx/2/compile.log`.
Source snapshot: `52f0554e47a3805643de4b9337ec2b28d1d6474e`.

`native-build src/app/_cg/f06/main.spl --emit-object --backend=cranelift --threads 4` launches three MIR workers for one module. Owner `0/3@0` claims and passes that module. Owners `1/3@0` and `2/3@0` claim nothing, then call native emission with no MIR. The ordinary empty-input guard rejects both workers. The aggregate records one completed worker, two failed workers, zero failed modules and zero unfinished modules. The same diagnostic appears for f07, f08, f08b, f08c, f08v and p3 entries; their independent source semantics are not established by this diagnosis.

The worker now skips emission only after successful lowering, successful borrow checking, zero compiler errors, accepted storage registration, zero claims and zero retained MIR modules. It still completes its ledger owner receipt and checks failed seals and completion errors. Claimed work with missing MIR still enters native emission and retains its failure guard. No module is excluded and no module PASS is manufactured for an idle worker.

Regression: `sh scripts/check/check-mir-idle-worker.shs /absolute/candidate-simple /absolute/fresh-evidence-dir` from the candidate's admitted checkout and compatible runtime environment. It requires exactly three worker receipts, one real claim/PASS, two idle workers, no failed seals, and a nonempty relocatable ELF object with a defined main symbol. The harness shell syntax check and corrected-runtime execution passed. Existing attempt5 failures are retained and are not relabeled PASS.

## Corrected-producer evidence

Attempt6 evidence: `/tmp/simple-release-1.0.0-phase2-attempt6-idle-mir-evidence-20261029/receipt.env`, `run.log`, and `product/compile.log`. The admitted candidate SHA-256 is `72b21f6a771c5df38094af04863f9354328d8f95de0406dec641ac08e733a06d`. Source inventory before and after agrees with admission (`88d9a448e1c488b44f8831e525994b30b4f021df97dc7bbac45e307ea81894c7`); runtime and tool authorities remained unchanged.

The real regression completed three owners with one claim/PASS, two idle owners, zero failed workers and zero unfinished modules. It emitted a nonempty ELF relocatable object defining main. The object was not executed (`object_executed=false`). Astra reviewed the source fix without P0/P1/P2 findings.

This focused PASS does not qualify the full compiler/bootstrap: the final CLI still encounters the resource cap and nineteen runner rows remain blocked.
