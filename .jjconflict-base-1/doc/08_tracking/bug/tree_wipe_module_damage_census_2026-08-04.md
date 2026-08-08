# Tree-wipe damage census — surviving modules destroyed or truncated

**Date:** 2026-08-04  
**Status:** OPEN (inventory complete; 1 of 39 truncations restored)  
**Scope:** owned `src/` `.spl` only (vendor excluded)

## Why this exists

`main` was wiped to near-zero files twice in 24 hours, and reconstruction
afterwards was partly done by guessing. `src/lib/common/wine_vm_adapter.spl`
was re-grown as an 89-line stub with an invented API from a 15-line remnant
when the real module was 322 lines; that guessed declaration then made a
repo-wide arity census misreport 109 correct call sites as broken. The wine
family was found only by accident. This document is the systematic sweep, so
that whatever is not fixed is at least **enumerable** rather than rediscovered
years from now.

## Method — three axes, cross-checked

A single instrument has been wrong repeatedly in this repo, so nothing here
rests on one measurement.

1. **History axis.** Every historical blob at every current `src/**/*.spl`
   path, via `git rev-list --all --objects --filter=object:type=blob`
   (75,274 blob/path pairs over 13,929 files). Max historical size vs current.
   *An ordinary `git log --all` walk is NOT adequate here*: history
   simplification collapsed it to 1.16 versions/file and it saw only 2 of the
   7 real `wine_vm_adapter` blobs.
2. **Consumer axis.** For every module, the symbols its importers actually
   reference, checked against what the module exports — with transitive
   `export use` / `pub use` closure, multi-line `use x.{...}` blocks, and glob
   imports resolved.
3. **Deleted axis.** Modules that no longer exist at all but are still imported
   by live code. The history axis is blind to these — it only covers files that
   still exist — which is how `src/lib/common/format_utils.spl` was missed.

**A module counts as damaged only where the axes agree:** a symbol its
consumers reference, absent now, present in a historical version of that same
path, and defined *nowhere else* in current owned `src/`.

## False positives — measured, not estimated

| Stage | Modules flagged | Cause of the drop |
|---|---|---|
| Consumer axis, naive | 867 | — |
| + transitive `export use` closure | 208 | **671 (77.4%) were one-line re-export shims** that legitimately define nothing |
| + multi-line `use` blocks, `pub use`, facade `use` | 259 | recall *increased*; found 5 more real `wine_vm_adapter` gaps hidden in a multi-line import |
| + directory-symlink resolution | — | `src/compiler/mir` → `50.mir` etc.; on the deleted axis this alone cut 550 → 377 (31.5%) |
| ∩ history axis (symbol was historically defined AND is gone everywhere) | **66** | 193 of 259 unconfirmed |
| + rewrite-vs-truncation split | **39** truncations | 27 were divergent rewrites |

Independent third instrument: a raw grep of the real working tree (walked
without `-L`, symlinks skipped, inode-deduped → 14,014 files) for definitions
of a random sample of 124 confirmed-missing symbols across all 66 modules.

> **False-positive rate: 0 / 124 = 0.0%.** Every sampled symbol is genuinely
> defined nowhere in owned `src/`.

Corpus-level dedup also matters: 6,081 of 34,090 `.spl` paths (17.8%) are
test-tree aliases (`test/unit/` ↔ `test/01_unit/`), and `src/`+`test/` hold 48
symlinks, 24 of them directory symlinks. Counting without deduping inflates
every consumer count roughly 2x.

## Ground-truth validation

The census was required to rediscover the known damage independently before
any other output was believed. It did:

| Module | Census found | Known truth |
|---|---|---|
| `wine_vm_adapter.spl` | 90 cur / 323 hist | 89 / 322 ✓ |
| `wine_process_session.spl` | 81 cur / 1413 hist | 80 / 1412 ✓ |
| `wine_hello_exe.spl` | `wine_hello_exe_probe_manifest`, `_evidence`, `_vm` all flagged | ✓ |

It also found a fourth wine casualty not previously named:
`wine_nt_api_catalog.spl` (24,047 B now vs 62,441 B historical).

> The wine family is **owned by another lane and was not edited here.**

## Two traps that would have produced false verdicts

**Matcher gap.** A sibling lane's first pass matched only `fn NAME` and missed
the `me NAME(...)` method form, so live methods read as dead — 3 of its 4
reported casualties were false. This census was re-run with a hardened matcher
covering `fn`, `pub fn`, `static fn`, `me fn`, `me NAME(`, `impl`, `def`, and
all class/enum/trait/type/val/var forms (`me NAME(` occurs 3,624 times in
`src/`). Result: **0 of 589 confirmed symbols were cleared.** The gap does not
affect this census, because module-level symbols reached through
`use mod.{sym}` are never methods — but the check was necessary, not assumed.

**Rewrite ≠ truncation.** A large drop from historical max is *not* evidence of
damage. 27 of the 66 confirmed modules are divergent rewrites whose current
version carries substantial content the historical version never had;
restoring those wholesale would destroy newer work. Each module is therefore
scored on the fraction of its *current* non-comment lines absent from the
historical version. `text_painter.spl` (96% novel) is a rewrite — matching the
sibling lane's independent finding.

> **Caveat on the wine family:** `wine_vm_adapter.spl` scores 85% novel, which
> the heuristic labels REWRITE. That is exactly right mechanically and exactly
> wrong semantically: its novel content is the *guessed* API from the botched
> reconstruction, not newer legitimate work. A high novel-fraction distinguishes
> "different code" from "less code" — it cannot distinguish good new code from
> invented code. Judge those by whether the declaration is internally coherent.

## Ranked inventory — truncations (39)

`cur`/`hist` are line counts; `novel` is the share of the current file absent
from history (high = suspect a rewrite); `cons` counts deduped consumers.

| # | Module | Tier | cur | hist | syms gone | cons | novel |
|---|---|---|---|---|---|---|---|
| 1 | `src/lib/common/compress/utilities.spl` | peripheral | 167 | 487 | 20 | 2 | 18% |
| 2 | `src/lib/gc_async_mut/gpu/browser_engine/script/worker_api.spl` | web-render | 80 | 147 | 10 | 1 | 5% |
| 3 | `src/lib/common/wine_hello_exe.spl` | peripheral | 34 | 205 | 9 | 5 | 84% |
| 4 | `src/os/qemu_systest_contract.spl` | peripheral | 375 | 396 | 8 | 3 | 7% |
| 5 | `src/lib/gc_async_mut/gpu/browser_engine/script/navigator_api.spl` | web-render | 76 | 135 | 7 | 1 | 29% |
| 6 | `src/os/compositor/shared_mdi_framebuffer_scene.spl` | web-render | 241 | 514 | 5 | 2 | 46% |
| 7 | `src/lib/gc_async_mut/js/engine/interpreter.spl` | peripheral | 8 | 398 | 4 | 1 | 100% |
| 8 | `src/lib/nogc_async_mut/js/engine/interpreter.spl` | peripheral | 19 | 398 | 4 | 1 | 100% |
| 9 | `src/lib/blink/dom/node.spl` | web-render | 45 | 152 | 3 | 3 | 71% |
| 10 | `src/lib/gc_async_mut/gpu/browser_engine/dom_accessors.spl` | web-render | 1450 | 2073 | 3 | 3 | 11% |
| 11 | `src/lib/nogc_async_mut/http_server/request_validation.spl` | peripheral | 151 | 146 | 3 | 1 | 10% |
| 12 | `src/lib/common/text_advanced.spl` | peripheral | 19 | 1414 | 2 | 2 | 0% |
| 13 | `src/lib/common/win_fs/window_record.spl` | peripheral | 58 | 141 | 2 | 3 | 36% |
| 14 | `src/os/drivers/framebuffer/ramfb.spl` | peripheral | 323 | 418 | 2 | 2 | 2% |
| 15 | `src/app/fix/rules/impl/lint_spec.spl` | peripheral | 15 | 185 | 2 | 1 | 100% |
| 16 | `src/os/compositor/qemu_capture.spl` | web-render | 220 | 242 | 1 | 4 | 0% |
| 17 | `src/lib/gc_async_mut/gpu/browser_engine/style/animation.spl` | web-render | 545 | 473 | 1 | 3 | 31% |
| 18 | `src/lib/nogc_sync_mut/io/tcp.spl` | peripheral | 526 | 539 | 1 | 2 | 0% |
| 19 | `src/lib/common/wine_hello_fixture.spl` | peripheral | 22 | 168 | 1 | 2 | 100% |
| 20 | `src/lib/common/net/addr.spl` | security | 75 | 312 | 1 | 2 | 48% |
| 21 | `src/lib/common/gpu/device.spl` | peripheral | 35 | 151 | 1 | 2 | 88% |
| 22 | `src/os/compositor/text_render.spl` | web-render | 31 | 476 | 1 | 2 | 92% |
| 23 | `src/lib/content/feature/render_widget_host_view.spl` | web-render | 30 | 52 | 1 | 1 | 86% |
| 24 | `src/os/apps/simple_browser/simple_browser.spl` | peripheral | 18 | 49 | 1 | 1 | 50% |
| 25 | `src/os/compositor/host_compositor_entry.spl` | web-render | 7 | 985 | 1 | 1 | 100% |
| 26 | `src/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch.spl` | web-render | 806 | 772 | 1 | 1 | 8% |
| 27 | `src/lib/common/crypto/chacha20.spl` | security | 207 | 612 | 1 | 1 | 34% |
| 28 | `src/lib/common/hpack/encoder.spl` | peripheral | 202 | 202 | 1 | 1 | 12% |
| 29 | `src/lib/gc_async_mut/gpu/engine2d/font_owner.spl` | web-render | 37 | 36 | 1 | 1 | 58% |
| 30 | `src/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena.spl` | peripheral | 486 | 490 | 1 | 1 | 0% |
| 31 | `src/lib/nogc_async_mut/fs_driver/fat32_parsers.spl` | peripheral | 152 | 246 | 1 | 1 | 40% |
| 32 | `src/os/apps/browser_demo/browser_demo.spl` | peripheral | 44 | 451 | 1 | 1 | 77% |
| 33 | `src/lib/common/animation/spring.spl` | peripheral | 58 | 141 | 1 | 1 | 29% |
| 34 | `src/os/compositor/wm_action_applier.spl` | web-render | 94 | 422 | 1 | 1 | 30% |
| 35 | `src/os/apps/file_explorer/file_explorer.spl` | peripheral | 13 | 874 | 1 | 1 | 100% |
| 36 | `src/app/cli/main.spl` | peripheral | 18 | 983 | 1 | 1 | 100% |
| 37 | `src/app/mcp/cli_passthrough.spl` | peripheral | 430 | 370 | 1 | 1 | 45% |
| 38 | `src/lib/gc_async_mut/gpu/browser_engine/layout_core.spl` | web-render | 654 | 708 | 1 | 1 | 1% |
| 39 | `src/lib/gc_async_mut/gpu/browser_engine/script/console_api.spl` | web-render | 115 | 114 | 1 | 1 | 19% |

### Divergent rewrites — DO NOT restore wholesale (27)

Listed so nobody "fixes" them by reverting to history.

| Module | cur | hist | novel | cons |
|---|---|---|---|---|
| `src/lib/gc_async_mut/gpu/browser_engine/script/canvas_api.spl` | 259 | 1903 | 92% | 1 |
| `src/lib/common/wine_process_session.spl` | 81 | 1413 | 65% | 58 |
| `src/app/dashboard/main.spl` | 88 | 1272 | 76% | 2 |
| `src/lib/gc_async_mut/gpu/browser_engine/webgpu_resources.spl` | 133 | 704 | 75% | 7 |
| `src/lib/gc_async_mut/gpu/browser_engine/css.spl` | 270 | 606 | 97% | 2 |
| `src/lib/common/wine_vm_adapter.spl` | 90 | 323 | 85% | 9 |
| `src/lib/common/proton_runtime_subsystems.spl` | 72 | 124 | 96% | 3 |
| `src/lib/common/window_protocol/window_protocol.spl` | 108 | 145 | 84% | 4 |
| `src/lib/gc_async_mut/gpu/browser_engine/webgpu_context.spl` | 226 | 1193 | 66% | 3 |
| `src/lib/common/engine/units.spl` | 102 | 141 | 81% | 2 |
| `src/os/apps/terminal/terminal.spl` | 105 | 574 | 90% | 1 |
| `src/os/compositor/screenshot_compare.spl` | 106 | 529 | 82% | 2 |
| `src/lib/gc_async_mut/gpu/browser_engine/layout.spl` | 194 | 1851 | 91% | 3 |
| `src/lib/cc/entity/property_tree.spl` | 89 | 454 | 51% | 1 |
| `src/app/doc_coverage/analysis/sdoctest_coverage.spl` | 81 | 546 | 78% | 2 |
| `src/lib/hardware/rv64gc_rtl/core.spl` | 763 | 570 | 59% | 1 |
| `src/lib/common/win_fs/fs_encoder.spl` | 106 | 338 | 76% | 1 |
| `src/lib/common/base_encoding/utilities.spl` | 143 | 342 | 91% | 1 |
| `src/lib/gc_async_mut/gpu/browser_engine/paint.spl` | 135 | 543 | 80% | 3 |
| `src/os/apps/file_manager/file_manager.spl` | 144 | 601 | 84% | 1 |
| `src/lib/common/engine/ids.spl` | 80 | 165 | 77% | 1 |
| `src/os/apps/hello_world/hello_world.spl` | 69 | 166 | 80% | 1 |
| `src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl` | 303 | 336 | 96% | 1 |
| `src/lib/common/crypto/poly1305.spl` | 284 | 375 | 57% | 1 |
| `src/lib/gc_async_mut/gpu/engine2d/helpers_text.spl` | 291 | 249 | 77% | 1 |
| `src/os/compositor/display_backend.spl` | 70 | 529 | 81% | 1 |
| `src/lib/common/math/bignum/bignat.spl` | 292 | 467 | 72% | 1 |

## Deleted modules still imported by live code

377 module names are imported by live code and resolve to nothing; 278 had
≥100 lines historically. This axis has a **higher residual false-positive
rate** than the other two, because Simple's module resolution has rules this
sweep does not fully model (numeric layer-prefix directories such as
`10.frontend`, plus loader search paths) — several top entries such as
`compiler.core.ast` almost certainly resolve at build time. Treat as leads to
verify, **not** as a fix list. The confirmed one is `format_utils`.

| Module name | was | hist lines | live importers |
|---|---|---|---|
| `compiler.core.ast` | `src/compiler/core/ast.spl` | 1188 | 109 |
| `compiler.core.parser` | `src/compiler/core/parser.spl` | 3654 | 77 |
| `compiler.backend.native.mach_inst` | `src/compiler/backend/native/mach_inst.spl` | 754 | 41 |
| `compiler.backend.backend_api` | `src/compiler/backend/backend_api.spl` | 798 | 35 |
| `compiler.core.tokens` | `src/compiler/core/tokens.spl` | 511 | 33 |
| `units.size` | `src/lib/std/src/units/size.spl` | 364 | 26 |
| `app.ffi_gen.intern_codegen` | `src/app/ffi_gen/intern_codegen.spl` | 305 | 24 |
| `compiler.backend.llvm_target` | `src/compiler/backend/llvm_target.spl` | 364 | 22 |
| `compiler.mir_opt.mod` | `src/compiler/mir_opt/mod.spl` | 355 | 21 |
| `compiler.backend.llvm_ir_builder` | `src/compiler/backend/llvm_ir_builder.spl` | 1284 | 21 |
| `units.file` | `src/lib/std/src/units/file.spl` | 565 | 17 |
| `app.ffi_gen.types` | `src/app/ffi_gen/types.spl` | 432 | 16 |
| `app.ffi_gen.module_gen` | `src/app/ffi_gen/module_gen.spl` | 174 | 16 |
| `common.ui.session` | `src/lib/common/ui/session.spl` | 596 | 16 |
| `compiler.backend.common.type_mapper` | `src/compiler/backend/common/type_mapper.spl` | 212 | 15 |
| `compiler.blocks.value` | `src/compiler/blocks/value.spl` | 258 | 13 |
| `compiler.backend.llvm_type_mapper` | `src/compiler/backend/llvm_type_mapper.spl` | 234 | 13 |
| `common.render_scene.executor` | `src/lib/common/render_scene/executor.spl` | 841 | 12 |
| `compiler.dependency.macro_import` | `src/compiler/dependency/macro_import.spl` | 285 | 12 |
| `hardware.rv64gc.ext.rv64_float` | `src/hardware/rv64gc/ext/rv64_float.spl` | 602 | 12 |
| `app.mcp_jj.helpers` | `src/app/mcp_jj/helpers.spl` | 142 | 11 |
| `common.ui.glass_test_page` | `src/lib/common/ui/glass_test_page.spl` | 412 | 11 |
| `compiler.blocks.definition` | `src/compiler/blocks/definition.spl` | 343 | 10 |
| `compiler.blocks.context` | `src/compiler/blocks/context.spl` | 233 | 10 |
| `compiler.blocks.modes` | `src/compiler/blocks/modes.spl` | 406 | 10 |
| `compiler.backend.vhdl.vhdl_builder` | `src/compiler/backend/vhdl/vhdl_builder.spl` | 360 | 10 |
| `compiler.backend.cuda_backend` | `src/compiler/backend/cuda_backend.spl` | 625 | 10 |
| `std.parser.treesitter` | `src/std/parser/treesitter.spl` | 277 | 10 |
| `hardware.rv64gc.ext.rv64_double` | `src/hardware/rv64gc/ext/rv64_double.spl` | 623 | 10 |
| `std.blink.layout.block_flow` | `src/lib/blink/layout/block_flow.spl` | 190 | 10 |

### Confirmed second-order casualty: `format_utils`

`src/lib/format_utils.spl` is live and does `export use lib.common.format_utils.*`,
but **`src/lib/common/format_utils.spl` does not exist** — it had a 15,819-byte
history. So `use std.format_utils.{...}` resolves to a facade pointing at
nothing. Because an unresolved `use` is only a WARNING (exit 0), this has been
silently broken. It is also why `wrap_text` could not be reached from
`text_advanced.word_wrap`: `wrap_text` now lives in
`src/lib/*/cli/formatting.spl`. **Not fixed here** — the right target tier for a
`common`-tier consumer needs a decision, and this census will not guess it.

## Restored

### `src/lib/common/text_advanced.spl` — 19 → 1,413 lines

The single cleanest case in the census, and the only one restored.

- **Damage was self-documented.** The stub's own header read: *"The full module
  was removed by commit 2cca0bc; this restores the self-contained, widely-imported
  helpers. TODO(text): restore the remaining text_advanced helpers from 2cca0bc~1."*
- **Nothing newer was at risk: novel-fraction 0%.** All 10 non-comment lines of
  the stub appear verbatim in the historical version — a strict subset, so the
  restore is provably non-destructive. This was checked *before* restoring.
- **Authoritative source:** blob `a0990f1c70c76af45d7661288311aa2f9e4db3fb`
  (39,684 B, 1,413 lines, 60 functions) — the largest of 21 historical versions.
  The API was taken from history and verified against the live consumer; **it was
  not reconstructed.**

**Proof by value** — `test/03_system/helpers/text_helpers_p1_spec.spl`:

| | blocks | examples | failures | exit |
|---|---|---|---|---|
| before | 9 | 39 | **39** | 1 |
| after | 9 | 39 | **0** | 0 |
| sabotage (`join("-")` → `join("~SABOTAGE~")`) | 9 | 39 | **5** | 1 |

Example **count** is identical across all three runs (9 blocks / 39 examples),
so no `describe` block was silently dropped. The sabotage run failed with
`expected hello~SABOTAGE~world to equal hello-world`, proving the spec really
exercises the restored code rather than passing vacuously.

One genuine defect surfaced in the restored code and was fixed in the same
change: `to_pascal_case` fed raw words to `str_capitalize`, which upper-cases
only the leading character and leaves the rest alone, so `"HELLO_WORLD"` gave
`"HELLOWORLD"`. The contract was **not guessed** — the function's own embedded
sdoctest pins `to_pascal_case("HELLO_WORLD") == "HelloWorld"`, and `.lower()`
is already the in-module idiom (line 718).

## Not restored, and why

- **The wine family (5 modules).** Another lane owns it; editing would collide.
- **The 27 divergent rewrites.** History is not authoritative for these.
- **The remaining 38 truncations.** Each needs its own by-value proof; several
  are facades whose one flagged symbol is a resolution artefact rather than
  damage (e.g. `host_compositor_entry.spl` at 7 lines is a deliberate facade,
  not a wipe — verified by reading it).
- **`format_utils`.** No authoritative answer for which tier should own it.

## Highest-value remaining targets

Ranked by blast radius, for whoever picks this up:

1. `src/lib/common/compress/utilities.spl` — 167/487, **20 symbols gone**,
   18% novel: SIMD tier dispatch, `crc32_bytes_*`, `xxhash32_bytes_*`.
   Lowest novel-fraction of any large truncation ⇒ best restore candidate.
2. `src/lib/gc_async_mut/gpu/browser_engine/dom_accessors.spl` — 1450/2073,
   11% novel, web-render pipeline.
3. `src/lib/common/crypto/chacha20.spl` — 207/612, security tier.
4. `src/os/qemu_systest_contract.spl` — 375/396, 8 `harden_*` symbols, 7% novel.

## Reproducing

The census is three passes over git objects plus one grep of the working tree;
it needs no build. The load-bearing details, in order: enumerate blobs with
`rev-list --objects` (**not** `git log`); dedupe test-tree aliases; resolve the
24 directory symlinks; take the transitive `export use` closure including
multi-line blocks; require agreement between the history and consumer axes;
then split truncation from rewrite by novel-line fraction.

