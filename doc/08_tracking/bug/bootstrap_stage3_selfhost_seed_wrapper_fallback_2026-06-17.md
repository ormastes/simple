# Bootstrap Stage 3 self-host fails — stage2 `bootstrap_main` binary can only emit a seed-wrapper, not real native code

- **Id:** bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17
- **Status:** Open
- **Severity:** P2 (self-host verification is skipped on every full bootstrap;
  Stage 4 silently falls back to the Rust seed, so the produced
  `build/bootstrap/full/<triple>/simple` is never the self-hosted compiler. The
  reproducible-build guarantee — stage2 SHA256 == stage3 SHA256 — cannot be
  checked. Not a runtime-correctness bug; the seed-built artifacts are valid.)
- **Found:** 2026-06-17 (full-bootstrap regression verification for the JIT
  composite extern-return fix, commit `49ca9697987`; reproduced across two
  consecutive `scripts/bootstrap/bootstrap-from-scratch.sh` runs)
- **Component:** bootstrap pipeline / self-hosted native-build
  (`bootstrap_main.spl`, `native-build` lowering/codegen, cranelift backend)
- **Files:**
  - `scripts/bootstrap/bootstrap-from-scratch.sh` (Stage 3 driver + warning text)
  - `src/app/cli/bootstrap_main.spl` (minimal CLI entry used for stage2/stage3)
  - `build/bootstrap/logs/<triple>/stage3-native-build.log`

## OBSERVED

A full bootstrap (cranelift backend, LLVM 18 absent) runs the manual pipeline
`seed → bootstrap_main → bootstrap_main`. Stage 3 (the self-host step:
stage2 binary recompiles `bootstrap_main.spl`) fails with exit 1, and the
pipeline falls back to the Rust seed for Stage 4:

```
Stage 3: stage2 → bootstrap_main.spl (self-host)
  warning: stage3 self-host failed (exit 1); using seed for stage 4
Stage 3 unavailable — using seed for stage 4
Stage 4: compiling full CLI (main.spl) with bootstrap compiler...
```

The proximate error in `stage3-native-build.log` is **not** an LLVM symbol
conflict — it is a guard refusing to emit a seed-wrapper:

```
error: bootstrap_main cannot emit a seed-wrapper fallback for build/bootstrap/stage3/<triple>/simple
error: rebuild with the full Simple driver so native-build uses real Simple lowering/codegen
```

The final bootstrap warning attributes the failure to **LIM-010 (LLVM symbol
conflicts)** per `doc/09_report/bootstrap_crash_report_2026_04_01.md`:

```
WARNING: Bootstrap produced a binary but self-host verification (stage 3) failed.
  The stage2 binary cannot yet recompile itself (LIM-010: LLVM symbol conflicts).
  Stage 4 used the Rust seed instead of the self-hosted compiler.
```

## ROOT CAUSE (proximate)

The Stage 2 binary is compiled from `bootstrap_main.spl` — the **minimal** CLI
entry. That binary does not carry the full Simple native lowering/codegen path,
so when asked to `native-build` itself in Stage 3 it can only produce a
*seed-wrapper fallback* (a thin shim that re-invokes the seed) rather than a real
native binary. A guard in the native-build path rejects the seed-wrapper for the
stage3 output and exits 1.

This is distinct from LIM-010 (the historical LLVM-CommandLine-option /
static-constructor conflict at self-hosted-binary startup). The script's warning
text conflates the two: the *current* proximate cause is the seed-wrapper guard
on the minimal `bootstrap_main` entry, regardless of backend.

## REGRESSION NOTE

`doc/09_report/bootstrap_crash_report_2026_04_01.md` records a state where Stage 3
self-host **worked and was SHA256-reproducible**:

```
Stage 3: stage2 → bootstrap_main.spl   ✓ (100 files, 0.8s compile — SELF-HOST WORKS)
  stage2 SHA256 == stage3 SHA256        ✓ (REPRODUCIBLE BUILD)
```

As of 2026-06-17 that no longer holds on `main` (cranelift path). Whether stage3
ever succeeds again depends on `bootstrap_main.spl` gaining the real
lowering/codegen path (or stage2/stage3 being built from the full driver entry).

## REPRODUCTION

```bash
sh scripts/bootstrap/bootstrap-from-scratch.sh
# inspect:
cat build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log
```

Deterministic: two back-to-back runs on 2026-06-17 produced byte-identical stage
progression; the second skipped the cargo rebuild via input-content-hash match,
confirming the failure is independent of any Rust-seed source change.

## IMPACT / WORKAROUND

- The bootstrap still produces working binaries (Stage 4 uses the seed, which is
  a correct compiler). Runtime correctness is unaffected.
- The lost guarantee is **self-host verification** (stage2 == stage3 SHA256) and
  shipping a genuinely self-hosted `build/bootstrap/full/<triple>/simple`.
- No source-side workaround; it is a pipeline/entry-capability gap.

## PROPOSED FIX OPTIONS (hypotheses — verify against actual native-build path)

1. Build stage2/stage3 from the **full driver entry** (`src/app/cli/main.spl`)
   instead of `bootstrap_main.spl`, so the self-host binary carries real
   native lowering/codegen and can emit a true native artifact.
2. Add the missing native lowering/codegen path to `bootstrap_main.spl` so the
   minimal entry can `native-build` without a seed-wrapper fallback.
3. If self-host is intentionally deferred, make the Stage 3 warning state the
   **actual** proximate cause (seed-wrapper guard on the minimal entry) rather
   than attributing it to LIM-010, to avoid misdiagnosis.

## RELATED

- `doc/09_report/bootstrap_crash_report_2026_04_01.md` (LIM-010 + Stage 3 history)
- `doc/06_spec/test/03_system/compiler/stage3_segfault_fix_spec.md`
- `doc/08_tracking/bug/selfhosted_mcp_binary_segfault_2026-06-02.md`
