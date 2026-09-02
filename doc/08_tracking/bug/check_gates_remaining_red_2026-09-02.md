# Remaining RED check gates after the 2026-09-02 sanity sweep

**Status:** OPEN 2026-09-02 — four guards remain honestly RED after five
mechanical defects in the guards themselves were fixed.
**Severity:** Blocking promotion — none of these may be wired push-blocking yet.
**Path:** `bug` track.

## 0. Context that changes how every number below must be read

The checkout these were measured on is a **detached HEAD that is NOT a
descendant of `origin/main`** (`git merge-base --is-ancestor origin/main HEAD`
→ NO; merge-base `591aad1791e`). `git diff --stat origin/main HEAD` over
`src/lib src/compiler src/compiler_rust` is **39 files, 723 insertions, 919
deletions** — HEAD is *missing* upstream work on several paths.

Two REDs were purely that: `rules.sdl` (ERROR, digest-unbound) and 4 of the 18
`sffi-v2-authority` sub-guard failures were fixed at origin and absent here.
**Re-measure every row below on a tree rebased onto `origin/main` before acting
on it.**

## 1. `check-core-lib-purity.shs` — 19 real violations, 1 stale entry

```
FAIL — 976 file(s) scanned, 19 new violation(s), 1 stale baseline entry(ies)
```

Was `31 new / 13 stale` until `1893d6433e5` fixed a Windows path-normalization
defect in the guard (rg emitted `C:/…/src/lib/common\compress\brotli.spl` while
the baseline holds `src/lib/common/compress/brotli.spl`, so 12 baselined files
were counted as BOTH new and stale). The 19 are genuine.

New violations — a pure-core (`src/lib/common`) file declaring a syscall-class
`rt_(file|dir|process|env|io|net|tcp|udp|stdin|stdout|cli|exit|time|socket|http)*`
extern, or importing a host tier:

```
crypto/ecdsa_p256.spl                     debug/host_profile_target.spl
debug/ref_debug_session.spl               encoding/font_registry.spl
js/engine/runtime.spl                     perf/render_perf_receipt_v2.spl
renderdoc/backend_render_receipt_wire.spl spec/evidence/format/evidence_sidecar.spl
spec/evidence/format/exec_capture.spl     spec/evidence/format/file_capture.spl
torch/dyn_sffi_ops.spl                    ui/glass/theme.spl
ui/ui_frame_clock.spl                     ui/ui_scene_ports_v3.spl
ui/ui_web_packed_producer.spl             ui/widget_draw_ir.spl
ui/window_scene_draw_ir.spl               wine_gui_hello.spl
wine_precondition_fixture_builder.spl
```

Stale: `src/lib/common/ui/win_text_access.spl`.

**Unblock:** move each impure extern to a host tier (`nogc_sync_mut/**`) and
rewire callers; that is 19 independent refactors, not a baseline edit. The
stale entry may only be dropped in the same change that confirms the file is
clean. Do NOT clear this with `--generate-baseline`.

## 2. `check-seed-extern-registry.shs` — 1 compiler + 68 lib unregistered

```
FAIL — compiler_extern_total=232 unregistered=47; unregistered_compiler_NEW=rt_text_eq_any
       lib_extern_total=2139 unregistered=578; 68 unregistered_lib_NEW, 101 stale
```

`rt_smf_reader_` was dropped from this count by `0a812185fce`: `collect()`
grepped `extern fn rt_…` with `-o` and no `^` anchor, so it read the COMMENT
`# HISTORICAL. Six \`extern fn rt_smf_reader_*\` symbols used to be declared here`
(`src/compiler/70.backend/linker/smf_reader.spl:41`) as a declaration.

`rt_text_eq_any` is declared at
`src/compiler/70.backend/backend/llvm_lib_translate_expr.spl:18`.
**`src/compiler/70.backend/` is another agent's live lane this session was told
to coordinate away from**, so it was reported rather than edited.

**Unblock:** register `rt_text_eq_any` in
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`, then re-measure the
68 `src/lib` rows on a rebased tree — the section-(b) drift is large enough
that vintage skew must be excluded before any of it is treated as new debt.

## 3. `check-bodyless-block-parity.shs` — still divergent

```
FAIL — 8 case(s) checked, divergent: run/shapeA run/shapeC
       native-build/shapeB native-build/shapeD
  FAIL run/shapeA: accepted a bodyless if (output: 1)
  FAIL run/shapeC: accepted a bodyless if (output: 7)
  FAIL native-build/shapeB: build failed rc=1
```

Already tracked: `doc/08_tracking/bug/seed_accepts_bodyless_if_native_build_rejects_2026-08-22.md`.
Recorded here only to confirm it reproduces on Windows at
`88ea1ede016`+ with `bin/simple.exe` md5 `d52d770724a9f8797e98ac7819709ab9`.

## 4. `check-sffi-v2-authority.shs` — 14 of 46 (down from 18)

`c97ec43195c` forward-synced 8 audit scripts from `origin/main`, recovering 4.
The remaining 14 belong to the active SFFI lane (`d3d3dd41b03`, `1b76db1d6c3`).
Several exit 1 with **no stdout at all** — e.g.
`sh scripts/audit/io-sffi-authority.shs` prints nothing and returns 1 — which is
the missing-verdict-line defect that lane is already repairing.

**Unblock:** that lane lands; then re-measure.

## Guards that went GREEN today

| guard | before | after |
|---|---|---|
| `check-rules-sdl.shs --group quick` | ERROR — not bound to policy digest | PASS — 11 gates checked |
| `check-interpreter-extern-registry-gap.shs` | FAIL — 0 new, 3 stale | PASS — 232 checked, 0 new, 0 stale |
| `check-type-walk-constructor-parity.shs` | FAIL — Function Pointer Union | PASS — 12 constructors, 0 unprojected |
