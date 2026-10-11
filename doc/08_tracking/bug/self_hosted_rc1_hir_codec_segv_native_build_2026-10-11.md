# Self-hosted rc.1 binary SIGSEGV in `hc_enc_hir_module` on any native-build of the current release_phase3 tree (darwin-aarch64, 2026-10-11)

- **Filed:** 2026-10-11 (release_phase3 consolidation lane, cherry-pick PR #3104 verification)
- **Status:** OPEN — toolchain/binary drift; needs a rebuilt self-hosted compiler
  (receipt-gated bootstrap) or a source fix confirmed against a fresh build
- **Host:** darwin-aarch64 (Apple Silicon), binary `bin/release/darwin-aarch64/simple`
  (pure-Simple self-hosted v1.0.0-rc.1, built 2026-09-18)
- **Tree:** release_phase3 tip `cdde9988a9a` (post-#3104); reproduces identically at
  unmodified base `94567b95ed7`, so the cherry-pick content is NOT the cause

## Symptom

Every `native-build` of the current tree dies ~8 s in, right after
`[bootstrap-error-count] source_idx=0 point=post-diagnostics count=0`:

```
Segmentation fault: 11 (exit 139)
```

lldb (from a tree checkout, stripped binary — one symbolized frame):

```
* thread #1, stop reason = EXC_BAD_ACCESS (code=1, address=0x94249550)
    frame #0: simple-bin`src__compiler__hir__generated__hir_codec__hc_enc_hir_module + 1460
->  ldr x8, [x8]        ; x8 = poisoned/non-canonical pointer
```

## Scope of the repro

- `native-build --source src/compiler --source src/app --source src/lib
  --entry-closure --entry src/app/mcp/main.spl` — SIGSEGV.
- `native-build --source src/lib --source examples --entry
  examples/01_getting_started/hello_native.spl` — SIGSEGV at the identical
  point. **Any** entry reproduces; the crash is not input-specific.
- Preceding log lines carry `hir-reexport-chase-unresolved` /
  `hir-callable-dep-origin-unresolved` advisories for primitives (`bool`,
  `i32`, `text`, `Option`, `Dict`) against
  `lib.nogc_sync_mut.debug.remote.session_model` / `app.mcp.dap_bridge`
  facades — consistent with the old resolver leaving poisoned HIR nodes that
  the encoder then dereferences unguarded.
- `check src/compiler` (6/6 OK) and `check src/lib` (24/24 OK) pass; the crash
  is specific to the HIR-serialization (cache/shard) path used by native-build.

## Ruled out

- **Cherry-pick content (#3104):** crash reproduces at the unmodified base.
- **Tree corruption:** `check` lanes pass; the seed (Rust beta.14) fails only on
  grammar drift (`windows_redirected_process.spl` parse), which is expected for
  a binary this old and confirms the tree has moved past the binary.

## Likely cause

Binary drift: the 2026-09-18 rc.1 compiler predates ~3 weeks of HIR/codec and
resolver changes on release_phase3. Two candidate root causes, to be
distinguished by a fresh self-hosted build:

1. Pure drift — a compiler built from the current tree encodes the current
   tree's HIR fine. Fix = rebuild/re-deploy `bin/release/<triple>/simple`
   (bootstrap receipt gate is the owner ceremony; CI deploy lanes normally own
   this).
2. A live source defect in `src/compiler/20.hir/generated/hir_codec.spl`
   (nil-unsafe encode of an unresolved/poisoned HIR node) that a fresh build
   would hit too. If so, the encoder must become fail-closed/nil-safe the way
   PR #2943 made provider relocation nil-safe.

## Evidence

- Repro log: `[bootstrap-error-count] ... post-diagnostics count=0` then signal 11.
- lldb single-frame backtrace above (binary is `--strip`, so no deeper frames).
- Sibling family: `stage2_test_runner_build_mir_segv_aarch64_2026-10-11.md`
  (FIXED by #2943, same nil-guard pattern class).
