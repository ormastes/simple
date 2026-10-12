# Seed compiled coalesce duplicates a stateful operand

Date: 2026-10-12. Status: OPEN compiler defect; caller workaround committed and Phase1 encoder regression passed.
Bug key: `seed_coalesce_stateful_operand_twice_2026_10_12`.
Owner scopes: Rust seed HIR lowering; generated pure-Simple AST semantic hash finish and its generator.
Qualified bug database reconciliation: pending; no callable qualified bug-database tool was available. This report is not a database success receipt.

## Actual failure and limits

The real generated ShellCommand encoder regression failed under pinned bootstrap seed `6b133a15211e2ffb7c8c289a151400dc9a173e70b72e1c9f2feb6589e5dd0e0e`. Its second, corrected fixture uses production `ast_semantic_hash_finish`; native exit was 11, final Windows Job active count 0, peak RSS 137776 KiB, and inputs remained unchanged. It printed `ENCODER_FINISHED cacheable=true bytes=-1` twice. The first fixture's incorrect optional-to-text return contract was corrected before this attempt; the second failure remains real and unresolved.

Evidence packet: `build/native_probe/phase1-shell-encoder-20261012-root`, `REQUEST2.json`, `RESULT2.json`, `encoder-run2/receipt.env`, and `encoder-run2/child.log`. Log SHA-256: `4b391352f1b0c95a68f721ee56b6d7977b6dad9a34381541a46d6b7c129ab9d1`. `RESULT2.json` SHA-256: `98adc145b16a824646a839c5802dedc3334c863dc9f8bc6f842b1b09b44e5f59`.

The separate real-owner storage test passed and must not be replayed. Native serializer parity remains unexecuted after its separate MIR compile failure. No performance, SHA-algorithm, full-suite, or compiler-wide failure claim follows from this report.

## Source diagnosis

`src/compiler/10.frontend/generated/ast_semantic_value.spl:53` finishes with a direct `sha256_stream_v1_finish_hex(state.stream) ?? ""`. `src/lib/common/crypto/sha256.spl:561` sets the stream's finished flag on its first call, returning `Some(hex)`; a second call returns nil.

Seed `src/compiler_rust/compiler/src/hir/lower/expr/control.rs`, `lower_coalesce`, inserts `expr_hir.clone()` into the condition and the original expression into the true branch's `rt_unwrap_or_self`. A stateful call is therefore represented twice. The runtime unwrap preserves nil, and `rt_string_len` returns -1 for non-string input. This source chain explains the observed failure, but deployed binary instruction-level attribution has not yet been demonstrated.

The AST interpreter evaluates the operand once. The pure-Simple HIR preserves `NullCoalesce(left,right)` and its MIR lowering at `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:4306` calls `self.lower_expr(left)` once, stores the result, and lowers the fallback only after selecting its else block. The matching duplicated-evaluation defect was not found in that pure-Simple path.

Seed provenance limit: `src/compiler_rust/target/bootstrap/simple.exe.inputs.sha256` binds the actual seed hash to aggregate input fingerprint `e0e240a45449714d12529a1e842b66ce2685cfaffd3a91c49d2936d267329ac6`; its details file contains category digests, not an individual authenticated mapping for this owner. The working source hashes are preserved in the private diagnosis receipt. A matching aggregate stamp is not proof that each inspected working source file produced the seed.

## Tagged workaround and true repair

Private proposals are under `build/native_probe/mir-json-perf-review-20261012-astra/layout-cache-followup/encoder-return-diagnosis/`:

* `canonical-workaround-v3/canonical-workaround.patch` (SHA-256 `23576f649efd5fc3b79c6396d77805c2283346a30d217faf9ac484eb71cb6fa4`) binds `val digest = sha256_stream_v1_finish_hex(state.stream)` before coalescing the local. The immediately preceding canonical tag is `# @workaround bug=seed_coalesce_stateful_operand_twice_2026_10_12 recover=0defcbb2ec87ac187e480c618b3b23f9818f1f7b reason=seed_coalesce_evaluates_stateful_operand_twice`. The actual generator emits exactly the proposed production function. This is a caller workaround, not a repaired seed compiler. Earlier private versions are preserved and superseded.
* `seed-lowering-proposal-v2/single-evaluation.patch` (SHA-256 `47ab33ef1e9643bddbe60a5740a09d2d6a9ceba1bc960333c0492c7fc7baac09`) proposes a private temporary HIR local and a block containing one store plus the coalesce expression. It immediately restores the generated name's previous mapping, preserving the local slot but avoiding leakage through the flat scope map. The existing non-nullable scalar fast path and lazy fallback remain intact. This separate Rust owner proposal is uncompiled and unrun; it has not modified shared source or a deployed binary.
* `seed-lowering-proposal/coalesce_evaluate_once.spl` uses real mutation counters for present, absent, and locally bound operands. It requires one left-side execution, no fallback for a present operand, and exactly one fallback for nil. It is unrun and is not a replacement for the real encoder assertions.

Recovery linkage: original fixture source commit `812442947d9cfc8448809c00a562c9468a17d103`; intended source/hunk recovery commit [0defcbb2ec87ac187e480c618b3b23f9818f1f7b — local commit, remote publication pending](https://github.com/ormastes/simple/commit/0defcbb2ec87ac187e480c618b3b23f9818f1f7b); actual caller workaround commit [4f5cf392ec9f9d98aeb3a1612a20e36aa8cc1c2b — local commit, remote publication pending](https://github.com/ormastes/simple/commit/4f5cf392ec9f9d98aeb3a1612a20e36aa8cc1c2b); actual compiler-fix commit **PENDING**. Both linked identifiers are currently local and unpushed; the links identify intended remote locations, not published commits. The workaround commit contains exactly the generated finish and generator hunks; unrelated dirty generated registry-hash edits were preserved. The two production owners and seed lowering owner are unchanged between 8124429 and 0defcbb. The `recover=0def...` tag identifies intended-source hunk recovery only; restoring that whole historical file would also discard unrelated later changes. It is not a claim that 0defcbb repairs the compiler. Remove the workaround only after the repaired compiler is admitted and the real encoder regression passes without it.

## Verified caller recovery — final encoder attempt3

Root's admitted, failed-only attempt3 used the actual generated production owner with the canonical tagged workaround, the unchanged corrected real encoder fixture, and the actual pinned seed. It passed all four digest-length checks with `cacheable=true bytes=64` and printed `SHELL_COMMAND_REAL_ENCODER_PASS`; native exit 0, final Job active count 0, peak RSS 139048 KiB. All 31 frozen inputs remained unchanged. Prior failed attempts remain preserved.

Receipt: `build/native_probe/phase1-shell-encoder-20261012-root/RESULT3.json`, SHA-256 `26a488dbd6a6d650193823dd0992b8f825a74638c8da8b3edfd37b03624ed626`. Actual log: `encoder-run3/child.log`, SHA-256 `1dfa0c9baa5d46fd68254b3476acf6bc32d8e652c723d53c29a6fd39ce960d4a`; process evidence in `encoder-run3/receipt.env`. This verifies the local caller workaround and real encoder outputs under Phase1. It does not establish a deployed seed lowering repair, native serializer parity, Phase3, full-suite, or performance qualification.

Encoder criterion attempts used: 3 of 3; criterion PASS and closed. Do not replay encoder or the separately passed storage test. True seed lowering proposals and their side-effect-count tests remain separate and unrun; qualified bug database reconciliation remains pending. The bootstrap snapshot at 0defcbb is now terminal before compiler start because of a collector RSS enumeration error, with its cycle3/attempt3 receipt preserved. That source snapshot remains unchanged; the caller workaround only enters a later rebuilt snapshot.
