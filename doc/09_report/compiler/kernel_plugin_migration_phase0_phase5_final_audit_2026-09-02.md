# Kernel Plugin Migration Phase 0/5 Final Audit

Date: 2026-09-02

## Selected Authority

- K1 policy: `llvm-cranelift`
- Simple ABI policy: `v1`
- Plugin manifest policy: `simple-sdn`
- Coverage cutover policy: `atomic-apk-only`
- Coverage implementation: `apk-only`

The canonical working-tree authority is `doc/04_architecture/compiler/plugin_arch/kernel_closure.sdn`.

## Results

- PASS: closure classification covers 1923 files with zero unclassified files.
- PASS: compiler-to-plugin and K0/K1-to-P imports are zero.
- PASS: typed K1 dispatch installs the sorted Cranelift, Interpreter, and LLVM table before the P-static table.
- PASS: the working tree contains only the selected LLVM+Cranelift composition root and only `simple.sdn` plugin manifests.
- PASS: K1 receipts bind policy, ABI v1, `simple.sdn`, atomic APK-only coverage, APK-only implementation, composition digest, authority path, and authority digest.
- PASS: receipt mutations reject 9/9 policy/evidence drifts; Phase 5 dispatch mutations reject 8/8 bypasses; closure selftests fail closed.
- FAIL: the current Jujutsu snapshot does not contain the working-tree authority manifest bytes.
- FAIL: the current Jujutsu snapshot still contains `src/compositions/kernel_cranelift_only/compiler/driver/bootstrap_k1_selected.spl`.

## Concrete Fixes

- Added Interpreter to K1 and removed it from the P-static backend registry.
- Removed the unselected Cranelift-only working-tree composition and candidate manifest alternatives.
- Restricted production authority to LLVM+Cranelift, ABI v1, `simple.sdn`, and atomic APK-only.
- Added receipt authority hashing and explicit K1 environment drift rejection.
- Changed the composition gate to compare worktree bytes with the committed snapshot and reject committed unselected roots.
- Extended the Phase 7 receipt consumer to verify manifest, coverage, coverage implementation, authority path, and authority digest.

## Evidence

Retained gate output is under `build/review/phase0_phase5_final/`.

The committed-state gate reports:

```text
FAIL — doc/04_architecture/compiler/plugin_arch/kernel_closure.sdn differs from the committed Jujutsu snapshot
FAIL — unselected committed composition remains: src/compositions/kernel_cranelift_only/compiler/driver/bootstrap_k1_selected.spl
```

Jujutsu cannot refresh the working-copy snapshot while `.git/index.lock` is held by concurrent repository activity. The lock was preserved rather than deleting or overriding another session's state.

## Verdict

`STATUS: FAIL` — 2 committed-state failures. No branch push or PR preparation is authorized until the snapshot is refreshed, this gate passes, Phase 2 is genuinely PASS, and the admitted self-hosted compiler completes the required MCP, LLM Caret, dev-tool, test, and provenance gates.
