# Non-Stage4 Bootstrap Lane — Regression Check After Today's HIR Fixes

Date: 2026-07-27 (all times UTC)
Scope: read-only evidence review. **No bootstrap was run for this report.**

Question: did today's stage-4 HIR-resolution fixes regress the NON-stage4 lane
(the path that builds MIR from the flat-AST accumulator via
`bootstrap_lower_to_mir_context`, `src/compiler/80.driver/driver.spl` ~L1107),
which stages 2 and 3 of every bootstrap depend on?

---

## 1. Why `nostage4.log` exited 1 — ROOT CAUSE

**Classification: codegen error (LLVM lowering name-classification), NOT an HIR
resolution failure and NOT a link failure or missing artifact.**

Evidence file: `/home/ormastes/.claude/jobs/4403a7d8/tmp/nostage4.log`
(26,353 bytes, 142 lines, mtime 2026-07-27 21:28:38 UTC).
Entry: `src/app/cli/main.spl`, all four source roots, **without**
`SIMPLE_BOOTSTRAP_STAGE4=1`.

The run reached the backend cleanly — the HIR-resolution axis this campaign was
fixing reported `me=0, unres=0, hir=0`, and the log contains **zero** `me`
receiver / unresolved-name errors (grep count 0). Everything before the failure
block is `warning: unresolved call ...` noise (`panic`, `DocBlock::Heading`,
`Tensor.*`), which is the same warning class stage 2 and stage 3 emit while
succeeding — see §2.

The terminating lines:

```
FAILED FILES (16):
...
Build failed: native-build aborted: 16 file(s) failed to compile
```

Breakdown of the 16:

| Kind | Count | Example |
|---|---|---|
| `llvm codegen: semantic: llvm global load referenced undeclared symbol X` | 14 | `env/paths.spl` → `variables`; `http_client.spl` and `http_client/response.spl` → `request`; `file_system/permissions.spl` → `file_ops`; `io/signal_handlers.spl` → `combined_cleanup`; `office/sheets/access_server.spl` → `StandaloneOptions`; the 7 `debug/remote/exec/adapter_*.spl` |
| `timeout (60s)` | 1 | `office/sheets/formula.spl` |
| `llvm codegen: semantic: ambiguous LLVM method resolution for to_f32` | 1 | `gpu/browser_engine/dom_color.spl` |

**This failure class is pre-existing and documented, predating today's fixes by
ten days.** `doc/08_tracking/bug/simple_shared_parameter_llvm_global_load_2026-07-17.md`
records the identical signature:

> During a full pure-Simple bootstrap, Stage 2 native-build failed for the HIP
> and OpenCL backend contract modules with:
> `llvm global load referenced undeclared symbol Shared`
> ... Lowercase local and parameter bindings named `shared` must remain local SSA
> values during LLVM lowering. They must not be canonicalized into a global or
> variant symbol named `Shared`.

A second instance is filed as
`doc/08_tracking/bug/native_entry_closure_call_type_args_undeclared_2026-07-19.md`.

Today's failing symbols fit that same shape exactly: `request`, `variables`,
`file_ops`, `combined_cleanup` are **sibling module / import names**, and
`StandaloneOptions` is a type name — identifiers that LLVM lowering
mis-canonicalises into a global load instead of resolving as a local or module
reference. The 07-17 bug's stated follow-up ("fix name classification so local
bindings take precedence over global/variant canonicalization") was never done.

The one timeout (`formula.spl`, 60s) is a per-file compile budget, not a
correctness signal.

**Conclusion for §1: `nostage4.log` exit 1 is NOT attributable to the five HIR
fixes.** It is a backend LLVM name-classification defect (bug of 2026-07-17,
still open) plus one compile-budget timeout. The HIR front-end the fixes touch
passed this run with `me=0, unres=0, hir=0`.

Residual uncertainty: no pre-fix baseline run of the same entry with the same
16-file set exists in the captured evidence, so "identical file list before the
fixes" is inferred from the bug-doc signature match, not directly diffed.

---

## 2. Stage 2 / Stage 3 positive evidence

Source: `/home/ormastes/.claude/jobs/4403a7d8/tmp/bootstrap.log`
(`--full-bootstrap --deploy`, finished 2026-07-27 13:56:36 UTC), and
`.../wt-bootstrap/build/bootstrap/logs/x86_64-unknown-linux-gnu/stage{2,3}-native-build.log`.

From `bootstrap.log`:

```
Stage 2: seed → bootstrap_main.spl
  stage2-native-build log: build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log
  Stage 2: running bootstrap compiler sanity
Stage 3: stage2 → bootstrap_main.spl (self-host)
  stage3-native-build log: build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log
  Stage 3 succeeded and passed bootstrap compiler sanity
  Stage 3 provenance: build/bootstrap/stage3/x86_64-unknown-linux-gnu/provenance.env
  Stage 2 native-build capability passed
stage2 sha256: ec1f46bc7c4c5fabadd356eb30b1cd82e512e1b150f784b0414a34f92cd2cb06
stage3 sha256: 1c19c59b62a46b4d3b4055b8125484fdab0a7716a65916946765a271679d49e2
warning: stage2 and stage3 hashes differ (expected when runtime is embedded)
  Using verified Stage 3 for stage 4
```

Stage 4 then failed, and only stage 4:

```
Stage 4: compiling full CLI (main.spl) with bootstrap compiler...
  stage4: clearing native cache (platform/backend/AOP build context changed)
error: stage4-native-build failed with exit 1
```

Per-stage tails (13:35 and 13:41 UTC respectively):

```
# stage2-native-build.log
Linked: .../build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple (123947 KB) via clang++
Build complete: 687 compiled, 0 cached, 0 failed
  Time: 71.9s compile + 64.0s link = 135.9s total

# stage3-native-build.log
Linked: .../build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple (123947 KB) via clang++
Build complete: 687 compiled, 0 cached, 0 failed
  Time: 299.2s compile + 56.7s link = 355.9s total
```

`grep -ciE 'undeclared symbol|FAILED FILES|Build failed'` over both stage logs
returns **0** for each. Also clean:

```
# stage2-capability.log
Build complete: 1 compiled, 0 cached, 0 failed
```

**Warnings present in stage 2/3 (benign, non-fatal):** the same
`warning: unresolved call \`panic\` in function backend__backend__cranelift_codegen_adapter__cl_translate_instruction`
family, plus `vulkan_backend.compile_gpu_instruction` / `compile_barrier` /
`compile_atomic` and `_MirToLlvm__aggregate_intrinsics.translate_call_indirect`.
These identical warnings appear in `nostage4.log` too, and both stage 2 and
stage 3 linked and passed compiler sanity with them present. They are noise,
not regression indicators.

The only bootstrap-level warning is the expected
`stage2 and stage3 hashes differ (expected when runtime is embedded)`.

---

## 3. Coverage matrix — which fixes were exercised by a passing stage 2/3

Timeline anchors (UTC):

| Event | Time |
|---|---|
| `9b612a11418` fix #1 committed | 13:09:01 |
| stage2-native-build.log written | 13:35 |
| stage3-native-build.log written | 13:41 |
| **bootstrap.log final write (stage 2+3 GREEN)** | **13:56:36** |
| `67024e9c0a5` fix #2 committed | 14:44:24 |
| **nostage4.log final write** | **21:28:38** |
| `8af2dc55596` fix #3 committed | 21:42:14 |
| `559832a135b` / `df7e0c50ced` fix #4 committed | 21:59:55 |
| `3eea09c6796` fix #5 committed | 22:01:29 |

| # | SHA | Subject | Files touched | Passing stage 2/3? | nostage4 HIR-clean run? |
|---|---|---|---|---|---|
| 1 | `9b612a11418` 13:09 | fix(hir): contains_key + index reads for struct-valued dict lookups | `20.hir/.../module_lowering.spl`, `module_registry.spl`, **`80.driver/driver.spl`** | **YES — covered** | yes |
| 2 | `67024e9c0a5` 14:44 | fix(hir): resolve facade re-exports and transitive star imports | `20.hir/.../module_lowering.spl` | **NO** (landed 48 min after bootstrap finished) | **yes** — reached codegen with `me=0, unres=0, hir=0` |
| 3 | `8af2dc55596` 21:42 | fix(hir): alias `me` <-> `self` when resolving a receiver | `20.hir/.../expressions.spl` | **NO** | **NO** (landed 14 min after nostage4) |
| 4a | `559832a135b` 21:59:55 | fix(hir): contains_key + index reads (reland/extend) | `20.hir/.../module_lowering.spl`, **`80.driver/driver.spl`** | **NO** | **NO** |
| 4b | `df7e0c50ced` 21:59:55 | fix(compiler): resolve module namespace calls safely | `20.hir/.../expressions.spl` (+ new regression spec) | **NO** | **NO** |
| 5 | `3eea09c6796` 22:01:29 | fix(driver): normalize symlink module spellings so package siblings match | **`80.driver/driver_source_loading.spl`** | **NO** | **NO** |

Note: the campaign was described as "five fixes" with four SHAs supplied; the
fifth landed in the 21:59:55 batch, so #4 is listed as the pair 4a/4b.

### Shared-code risk assessment

Most of the fixes live under `src/compiler/20.hir/hir_lowering/**`, which the
non-stage4 flat-AST → `bootstrap_lower_to_mir_context` path does not execute.
Two exceptions touch code shared by BOTH lanes:

- **`80.driver/driver.spl` (#1, #4a)** — both are pure *deletions* of the
  `hir_registry_reset()` / `hir_registry_put(...)` mirror that was itself added
  earlier today. Net effect on the non-stage4 lane is a revert to this
  morning's behavior, i.e. neutral. Low risk. Fix #1's version of this deletion
  is directly covered by the green stage 2/3.
- **`80.driver/driver_source_loading.spl` (#5)** — **highest risk, zero
  coverage.** It is *additive*: `_driver_module_aliases` now pushes two extra
  `SourceFile` alias spellings (`compiler.10.frontend.core.*` and
  `compiler.core.*`) for every file whose module name starts with
  `compiler.frontend.core.`. Source loading and alias registration are
  **lane-agnostic** — they run before the HIR/flat-AST fork, so this changes the
  module set every stage 2 and stage 3 build sees. It landed at 22:01, after
  every piece of evidence in this report. Nothing has exercised it.

---

## 4. Verdict

**AT RISK — specifically and only because of fix #5 (`3eea09c6796`); no evidence
of any actual regression, and the one observed failure is a pre-existing
backend bug.**

Supporting reasoning:

1. **`nostage4.log` exit 1 is not a regression signal for this campaign.** It is
   a codegen/name-classification failure whose signature is filed as an open bug
   dated 2026-07-17, plus one 60s compile timeout. The HIR front-end that the
   five fixes modify passed that same run with `me=0, unres=0, hir=0`.
2. **The non-stage4 lane demonstrably still worked with fix #1 in the tree:**
   stage 2 and stage 3 each compiled 687 files, 0 failed, linked, and passed
   bootstrap compiler sanity.
3. **Fixes #2–#5 have no passing stage 2/3 behind them.** #2 has weaker but real
   positive evidence (the 21:28 nostage4 run got clean through HIR to codegen
   with it in the tree). #3, #4a, #4b, #5 have none at all.
4. **Fix #5 is the one that can plausibly move the non-stage4 lane**, because it
   changes lane-agnostic source loading by injecting additional module-name
   aliases. Extra aliases could in principle produce duplicate module
   registrations or shift which spelling wins dedup for the flat-AST
   accumulator. This is a hypothesis, not an observation.

### To convert AT RISK → healthy

Run one `--full-bootstrap` (or a stage-2/stage-3-only pass) at or after
`3eea09c6796` and confirm both stage logs still report
`687 compiled, 0 cached, 0 failed` (file count may legitimately drift) plus
`Stage 3 succeeded and passed bootstrap compiler sanity`. That single run covers
fixes #2 through #5 at once. Explicitly out of scope for this report per
instruction.

### Separately worth filing / relanding

The 14 `llvm global load referenced undeclared symbol` failures are the unfixed
follow-up of `doc/08_tracking/bug/simple_shared_parameter_llvm_global_load_2026-07-17.md`.
They block the full-CLI build on both lanes and are independent of the stage-4
HIR campaign. The `office/sheets/formula.spl` 60s timeout and the
`dom_color.spl` ambiguous `to_f32` method resolution are two further distinct
defects in the same 16-file set.

---

## Evidence index

- `/home/ormastes/.claude/jobs/4403a7d8/tmp/nostage4.log`
- `/home/ormastes/.claude/jobs/4403a7d8/tmp/bootstrap.log`
- `/home/ormastes/.claude/jobs/4403a7d8/tmp/wt-bootstrap/build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`
- `/home/ormastes/.claude/jobs/4403a7d8/tmp/wt-bootstrap/build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
- `/home/ormastes/.claude/jobs/4403a7d8/tmp/wt-bootstrap/build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-capability.log`
- `/home/ormastes/dev/pub/simple/doc/08_tracking/bug/simple_shared_parameter_llvm_global_load_2026-07-17.md`
- `/home/ormastes/dev/pub/simple/doc/08_tracking/bug/native_entry_closure_call_type_args_undeclared_2026-07-19.md`
- `/home/ormastes/dev/pub/simple/doc/08_tracking/bug/bootstrap_stage4_hir_import_crash_2026-07-27.md`
- `/home/ormastes/dev/pub/simple/src/compiler/80.driver/driver.spl`
- `/home/ormastes/dev/pub/simple/src/compiler/80.driver/driver_source_loading.spl`
