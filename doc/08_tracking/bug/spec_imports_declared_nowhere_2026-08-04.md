# Spec imports that resolve to no declaration anywhere in owned `src/`

**Status:** ARCHITECTURAL/OUT-OF-SCOPE-OPEN (triaged 2026-08-10)  
**Filed:** 2026-08-04  
**Measured at:** `53492af8dc4bb95e8bb11c18ec813f63e065b479` (pristine detached worktree)  
**Tool used:** deployed `bin/release/x86_64-unknown-linux-gnu/simple` (Rust bootstrap seed — the only
binary deployed on this host; `bin/release/linux-x86_64/simple` does not exist)

## 1. Finding

`1003` distinct names are imported by `use` statements in `test/**/*_spec.spl` and are
**declared nowhere** in owned `src/` or `test/` `.spl` sources, across **294** distinct
spec files (`514` raw spec paths — the `test/01_unit/` and `test/unit/` trees are duplicates
of each other and are collapsed here).

An unresolved **name** inside a module that does resolve is only a **warning**, so these
specs load anyway. (An unresolved **module** is a hard error — measured verbatim:
`error: semantic: Cannot resolve module: common.wine_substrate`. The two are different
failure modes and only the first is silent.) The warning lands inside ~1,700 lines of
unrelated lint noise, so the reason the spec then fails — or quietly does nothing — is
invisible at the verdict line.

## 2. Method, and the two errors it corrects in the first pass

Census (`scratchpad/imp_census/census2.py`):

1. Parse **all three** import forms from every `test/**/*_spec.spl`: braced
   `use a.b.{X, Y as Z}` (incl. multi-line blocks), `use a.b.*`, and bare `use a.b`.
2. Build a declaration index over owned `src/` + `test/` `.spl` covering `fn class struct
   enum trait mixin actor interface type alias impl macro module val var let const global`
   at **any** indentation, plus four forms a line-start keyword grep misses: `me name(...)`
   receiver methods, bare module-level `NAME = value` constants, `export a, b, c` re-export
   lists, and enum variant bodies.
3. Resolve each `use` module path to a concrete file by reimplementing the resolver in
   `src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl` — `std.` -> `src/lib/`,
   the 10-family `nogc_*`/`gc_*` search order, `NN.name` numbered directories, and
   `__init__.spl` packages — so a name can be scored against the module it was actually
   imported from, not just repo-wide.

**Correction 1 — symlinked directories (this moved the number the most).**
`src/` contains symlinked directories (e.g. `src/app/t32_cli`). A recursive walk that does
not follow symlinks sees **13,931** of the **22,910** `.spl` files under `src/` — it is blind
to 39% of the tree. Every name declared under a symlinked directory therefore reads as
"declared nowhere". This one bug produced the two heaviest offenders in the first pass:
`test/01_unit/app/t32_cli/error_codes_spec.spl` (reported 29 missing names) is in fact
**fully clean** — `val T4001 = "T4001"` and its 28 siblings are declared in
`src/app/t32_cli/error_codes.spl`, and the spec measures `Results: 22 total, 22 passed, 0 failed`.
`t32_mcp_spec.spl` drops from 21 missing names to 1.
Any census over this repo must walk with symlinks followed and de-duplicate by realpath.

**Correction 2 — declaration forms.** Adding `me`-receiver methods, bare `NAME =` constants
and `export` lists removed a further 42 names.

### Independent confirmation

For each of the 1003 names, every occurrence of the identifier anywhere in owned `src/`
**outside** `use` lines was counted. **960 of 1003 (95.7%)** occur **zero** times — they are not
merely undeclared, they are entirely absent from the source tree. The remaining 43 appear
in some `src/` body and need per-name adjudication (a declaration form still not modelled,
or a genuinely dangling reference inside `src/` itself).

### Residual error modes

- **Undercount.** Only braced imports name their symbols, so a symbol missing behind a
  `use a.b.*` or bare `use a.b` is invisible to the name-level census. Those forms are
  counted at module level instead (§4).
- **Overcount risk.** A name re-exported through a chain of `export use` may be declared in
  a file the resolver does not reach. This is bounded by the independent confirmation above:
  a re-exported name would still appear somewhere in `src/`, and 95.7% of these do not.
- **Not scored.** Method names reached by UFCS/receiver dispatch rather than by import.
- The declaration index is *deliberately generous*: it errs toward calling something
  declared, so the count is a lower bound on the true breakage.

## 3. Classification

| class | specs | names | signal |
|---|---:|---:|---|
| (c) module absent — nothing to import from | 129 | 368 | the `use` target file does not exist at all |
| (a) module present, API surface never written | 156 | 606 | file exists; no near-name in it |
| mixed | 9 | 59 | spec imports from both |

### (b) renamed/moved symbol — **0 confirmed**

Every module-present missing name was fuzzy-matched (difflib, cutoff 0.82) against the names
actually declared in its resolved module. 46 of 719 produced a near-match; every one adjudicated was
a **sibling member of an unwritten surface, not a rename** —
`WEBGPU_BINDING_TYPE_STORAGE_TEXTURE` vs `WEBGPU_BINDING_TYPE_TEXTURE` are two different
constants, and `append_self_overlap_copy_{avx2,neon,scalar,for_tier}` are four SIMD tiers of
an existing untiered `append_self_overlap_copy`. Renaming the spec to the near-match would
make it assert against the wrong symbol. **No import here should be rewritten to a near-name.**

### (d) vacuously green — **CONFIRMED, 5 distinct specs measured green**

A spec that imports a nonexistent name *and never mentions it again* cannot fail because of
it, so it can pass while testing nothing — the worst class. Scoring every finding by whether
the name appears in the spec body outside `use` lines:

- **495 of 514** spec paths reference **every** one of their missing names in the body. Those
  cannot be vacuous: the reference must fail.
- **19** spec paths (13 after collapsing the duplicate test trees) reference **none** of them.
  These are the class-(d) candidates, listed in §5.1. Each carries 1 dead import.

**All 13 raw candidate paths were then run**, one spec at a time. **6 are green** — 5
distinct specs, since `immut/integration_spec` exists twice — and 7 are red. The static predictor is therefore
real, not a heuristic artefact, and the worst class does exist in this repo:

| spec | dead import | verbatim verdict |
|---|---|---|
| `test/unit/lib/crypto/chacha20_spec.spl` | `chacha20_keystream` | `Results: 12 total, 12 passed, 0 failed` |
| `test/unit/lib/immut/integration_spec.spl` | `Pipeline__new` | `Results: 20 total, 20 passed, 0 failed` |
| `test/unit/lib/common/immut/integration_spec.spl` | `Pipeline__new` | `Results: 20 total, 20 passed, 0 failed` |
| `test/unit/lib/common/proton_real_exec_spec.spl` | `proton_non_wine_runtime_evidence_new` | `Results: 11 total, 11 passed, 0 failed` |
| `test/feature/web_platform/css/animations_wpt_spec.spl` | `interpolate_keyframes` | `Results: 5 total, 5 passed, 0 failed` |
| `test/system/feature/language/modules_spec.spl` | `TlsStream` | `Results: 3 total, 3 passed, 0 failed` |

The crypto one is the sharpest: `test/unit/lib/crypto/chacha20_spec.spl:13` reads
`use std.crypto.chacha20.{chacha20_block, chacha20_encrypt, chacha20_keystream}`.
`chacha20_keystream` occurs in **zero** files under `src/` and exactly once in the spec —
on that `use` line. The spec reports 12/12 green having never touched the keystream API it
advertises. Same shape as `Pipeline__new`, whose sibling constructors in the very same
import block (`PersistentMap__empty`, `Atom__new`, `PersistentTrie__empty`) do exist, so the
`Type__ctor` convention makes the absence invisible on inspection.

For the other 281 specs the compiler fails closed: a spec whose import is missing *and
used* typically collapses to `Results: 1 total, 0 passed, 1 failed` — the whole file becomes
one failing example. The vacuity is confined to imports the spec never mentions again.

## 4. The larger, unattributable family: modules that resolve to nothing

Extending the census to `use a.b.*` and bare `use a.b` (which the first pass did not scan)
finds that spec files reference **782 distinct module paths** that resolve to **no file at
all**, over **2453** `use` sites — **66** star imports and **329** bare imports among them.
Heaviest: `verification.lean.codegen` (8), `verification.lean.naming` (8), `compiler.core.parser` (8), `compiler.core.ast` (8), `std.test` (8).
Each is a whole missing module, not a single name, so it deserves its own lane.

Two corrections were needed to get this number, and both are traps for the next lane:

1. The module regex accepts `.`, so `use std.spipe.*` parses as module `std.spipe.` with a
   **trailing dot**, which then resolves to a bogus `lib/spipe/.spl` and reads as unresolved.
   That single bug invented `std.spipe.` as the #1 offender with 1,105 phantom sites.
2. The **driver** resolves module paths relative to cwd, `src/`, **and `src/lib/`**
   (`src/compiler/80.driver/driver_source_pipeline_loading.spl:223`) — the interpreter's
   resolver in `module_loader_resolve.spl` does not list that third root. Omitting it makes
   `use common.ui.widget` look broken (there is no `src/common/`) when it resolves fine to
   `src/lib/common/ui/widget.spl`. This alone invented **269 modules / ~945 sites** of
   phantom "missing `std.` prefix" defects. Do **not** mass-rewrite `use common.X` to
   `use std.common.X`; it is already correct.

A genuinely unresolvable module is an **error**, not a warning — measured verbatim:
`error: semantic: Cannot resolve module: common.wine_substrate`. The warning-only behaviour
in §1 applies to an unresolved **name** inside a module that does resolve.

## 5. Measured verdicts

`SIMPLE_TIMEOUT_SECONDS=0 bin/simple test <spec> --timeout 3000`, one spec at a time,
verbatim final `Results:` line.

| spec | verdict |
|---|---|
| `test/01_unit/app/t32_cli/error_codes_spec.spl` | `Results: 22 total, 22 passed, 0 failed` |
| `test/03_system/feature/app/t32_tools/t32_mcp_spec.spl` | `Results: 1 total, 0 passed, 1 failed` |
| `test/01_unit/lib/blink/form_paint_spec.spl` | `Results: 1 total, 0 passed, 1 failed` |
| `test/01_unit/lib/common/wine_substrate_spec.spl` | `Results: 1 total, 0 passed, 1 failed` |
| `test/02_integration/hardware/rv32imac/rv32_core_smoke_spec.spl` | `Results: 1 total, 0 passed, 1 failed` |
| `test/01_unit/lib/common/compress_shared_helpers_spec.spl` | `Results: 7 total, 0 passed, 7 failed` |
| `test/01_unit/app/ui/display_detect_spec.spl` | `Results: 1 total, 0 passed, 1 failed` |
| `test/01_unit/app/ui/wire_golden/wire_golden_spec.spl` | `Results: 4 total, 2 passed, 2 failed` |
| `test/unit/lib/immut/integration_spec.spl` | `Results: 20 total, 20 passed, 0 failed` |
| `test/unit/lib/crypto/chacha20_spec.spl` | `Results: 12 total, 12 passed, 0 failed` |
| `test/unit/lib/common/proton_real_exec_spec.spl` | `Results: 11 total, 11 passed, 0 failed` |
| `test/unit/lib/common/immut/integration_spec.spl` | `Results: 20 total, 20 passed, 0 failed` |
| `test/unit/browser_engine/anonymous_block_spec.spl` | `Results: 4 total, 0 passed, 4 failed` |
| `test/unit/app/ui/unified_app_spec.spl` | `Results: 1 total, 0 passed, 1 failed` |
| `test/system/simpleos_desktop_framebuffer_spec.spl` | `Results: 4 total, 3 passed, 1 failed` |
| `test/system/command_history_spec.spl` | `Results: 1 total, 0 passed, 1 failed` |
| `test/feature/web_platform/css/animations_wpt_spec.spl` | `Results: 5 total, 5 passed, 0 failed` |
| `test/03_system/os/simpleos_desktop_framebuffer_spec.spl` | `Results: 4 total, 3 passed, 1 failed` |
| `test/03_system/gui/command_history_spec.spl` | `Results: 1 total, 0 passed, 1 failed` |
| `test/03_system/feature/language/modules_spec.spl` | `Results: 3 total, 3 passed, 0 failed` |
| `test/01_unit/os/__tmp_adapter_probe_spec.spl` | `Results: 3 total, 0 passed, 3 failed` |

### 5.1 Class-(d) candidates — dead imports, name never referenced in the body

| spec | dead import(s) |
|---|---|
| `test/feature/web_platform/css/animations_wpt_spec.spl` | `interpolate_keyframes` |
| `test/system/command_history_spec.spl` | `CommandMeta` |
| `test/system/feature/language/modules_spec.spl` | `TlsStream` |
| `test/system/gui/command_history_spec.spl` | `CommandMeta` |
| `test/system/os/simpleos_desktop_framebuffer_spec.spl` | `send_harness_marker` |
| `test/system/simpleos_desktop_framebuffer_spec.spl` | `send_harness_marker` |
| `test/unit/app/ui/unified_app_spec.spl` | `UnifiedApp` |
| `test/unit/browser_engine/anonymous_block_spec.spl` | `be_dom_get_tag_name` |
| `test/unit/lib/common/immut/integration_spec.spl` | `Pipeline__new` |
| `test/unit/lib/common/proton_real_exec_spec.spl` | `proton_non_wine_runtime_evidence_new` |
| `test/unit/lib/crypto/chacha20_spec.spl` | `chacha20_keystream` |
| `test/unit/lib/immut/integration_spec.spl` | `Pipeline__new` |
| `test/unit/os/__tmp_adapter_probe_spec.spl` | `_device_mapping` |

### 5.2 Sabotage proof — the braced import list is not enforced at all

`test/01_unit/lib/crypto/chacha20_spec.spl` was mutated one axis at a time and re-run.
Verbatim final `Results:` lines:

| # | mutation | verdict |
|---|---|---|
| 0 | unmodified baseline | `Results: 12 total, 12 passed, 0 failed` |
| 1 | the **unused** name `chacha20_keystream` -> `chacha20_keystream_XYZZY_DOES_NOT_EXIST` | `Results: 12 total, 12 passed, 0 failed` |
| 2 | the **used** name `chacha20_block` -> `chacha20_block_XYZZY_DOES_NOT_EXIST` (the body calls `chacha20_block(` twice) | `Results: 12 total, 12 passed, 0 failed` |
| 3 | the **module path** `std.crypto.chacha20` -> `std.crypto.chacha20_XYZZY_NO_SUCH_MODULE` | **`Results: 1 total, 0 passed, 1 failed`** |

Arm 2 is the result that reframes this whole report. Corrupting a name the spec **actively
calls** does not fail it. So the braced name list in a `use` is **decorative**: resolving the
MODULE registers its whole surface, and the names inside `{...}` are not checked against it.
(This is the same mechanism recorded in `reference_importing_one_symbol_registers_a_whole_module`,
here confirmed from the opposite direction.)

That is why 1003 phantom names produce only a warning, why the class-(d) specs are green, and
why a spec can advertise an API in its imports that has never existed. The import list is
documentation, not a contract — but it is read by humans, and by censuses like this one, as
if it were a contract.

**Consequence for triage:** do not treat "spec imports a missing name" as predicting a
failure. It predicts nothing about the verdict. It only tells you the spec's stated surface
and the module's real surface disagree.

## 6. Full classified inventory

`kind` = whether the module named in the failing `use` resolves to a file.
Paths are collapsed across the duplicate `test/01_unit` / `test/unit` trees.

| names | kind | spec | module(s) |
|---:|---|---|---|
| 344 | module present | `test/unit/browser/script/canvas_api_spec.spl` | `std.gc_async_mut.gpu.browser_engine.script.canvas_api`, `std.gc_async_mut.gpu.browser_engine.webgpu_resources` |
| 21 | mixed | `test/system/app/simpleos/feature/simpleos_wine_substrate_spec.spl` | `common.wine_hello_exe`, `common.wine_process_session`, `common.wine_substrate` |
| 17 | module absent | `test/unit/lib/blink/form_paint_spec.spl` | `std.blink.dom.form_state`, `std.blink.layout.block_flow`, `std.blink.paint.paint_tree_walker` |
| 17 | module present | `test/unit/lib/debug/remote/t32_ffi/t32_types_spec.spl` | `std.debug.remote.t32_ffi.t32_types` |
| 15 | module absent | `test/unit/lib/common/wine_substrate_spec.spl` | `common.wine_substrate` |
| 13 | module absent | `test/integration/hardware/rv32imac/rv32_core_smoke_spec.spl` | `hardware.riscv_common.core.riscv_decode`, `hardware.riscv_common.pkg.riscv_types_pkg` |
| 12 | module present | `test/unit/hardware/riscv_common/riscv_formal_contract_spec.spl` | `hardware.riscv_common.core.riscv_formal` |
| 12 | module present | `test/unit/lib/common/compress_shared_helpers_spec.spl` | `std.common.compress.utilities` |
| 11 | module absent | `test/unit/lib/blink/paint_tree_walker_spec.spl` | `std.blink.entity.computed_style`, `std.blink.layout.block_flow`, `std.blink.paint.paint_tree_walker` |
| 11 | module absent | `test/unit/lib/common/wine_precondition_fixture_builder_spec.spl` | `common.wine_precondition_fixture_builder` |
| 11 | module absent | `test/unit/lib/common/wine_service_adapter_spec.spl` | `common.wine_service_adapter` |
| 10 | module present | `test/unit/lib/gc_async_mut/gpu/browser_engine/css_ext_routing_spec.spl` | `std.gc_async_mut.gpu.browser_engine.css` |
| 10 | module present | `test/system/feature/web_platform/webgpu/webgpu_resources_spec.spl` | `std.gc_async_mut.gpu.browser_engine.webgpu_resources` |
| 10 | module present | `test/feature/web_platform/webgpu/webgpu_resources_spec.spl` | `std.gc_async_mut.gpu.browser_engine.webgpu_resources` |
| 10 | module present | `test/unit/browser/script/worker_api_spec.spl` | `std.gc_async_mut.gpu.browser_engine.script.worker_api` |
| 10 | module absent | `test/unit/hardware/rv64gc/rv64_fp_convert_d_spec.spl` | `hardware.rv64gc.ext.rv64_double` |
| 10 | module absent | `test/unit/hardware/rv64gc/rv64_fp_convert_s_spec.spl` | `hardware.rv64gc.ext.rv64_float` |
| 9 | module absent | `test/unit/app/test/chrome_component_renderer_parity/diagnostics_spec.spl` | `app.test.chrome_component_renderer_parity.diagnostics`, `common.ui.rendering_parity`, `common.ui.rendering_parity.checksum` |
| 9 | module absent | `test/unit/app/ui/display_detect_spec.spl` | `common.test_runner.display_detect` |
| 9 | module absent | `test/system/gui/container_detect_spec.spl` | `common.test_runner.display_detect` |
| 9 | module absent | `test/system/hardware/rv64gc_spec.spl` | `hardware.rv64gc.core.rv64_decode`, `hardware.rv64gc.core.rv64_execute`, `hardware.rv64gc.ext.rv64_atomics`, +2 |
| 9 | module absent | `test/system/rv64gc_spec.spl` | `hardware.rv64gc.core.rv64_decode`, `hardware.rv64gc.core.rv64_execute`, `hardware.rv64gc.ext.rv64_atomics`, +2 |
| 9 | module absent | `test/unit/lib/blink/image_paint_spec.spl` | `std.blink.layout.block_flow`, `std.blink.paint.paint_tree_walker` |
| 9 | module absent | `test/unit/lib/blink/inline_flow_spec.spl` | `std.blink.layout` |
| 9 | mixed | `test/unit/lib/common/wine_hello_exe_manifest_spec.spl` | `common.wine_hello_exe`, `common.wine_hello_fixture`, `common.wine_precondition_manifest` |
| 9 | module absent | `test/system/coverage/coverage_build_spec.spl` | `compiler.driver.build.coverage` |
| 8 | module present | `test/system/feature/web_platform/webgpu/webgpu_context_spec.spl` | `std.gc_async_mut.gpu.browser_engine.webgpu_context`, `std.gc_async_mut.gpu.browser_engine.webgpu_resources` |
| 8 | module present | `test/feature/web_platform/webgpu/webgpu_context_spec.spl` | `std.gc_async_mut.gpu.browser_engine.webgpu_context`, `std.gc_async_mut.gpu.browser_engine.webgpu_resources` |
| 8 | module absent | `test/integration/hardware/rv64gc/rv64_fp_compliance_spec.spl` | `hardware.rv64gc.ext.rv64_double`, `hardware.rv64gc.ext.rv64_float` |
| 8 | module absent | `test/unit/lib/blink/hit_test_spec.spl` | `std.blink.input.event`, `std.blink.input.hit_test`, `std.blink.layout.block_flow` |
| 8 | module present | `test/unit/lib/common/compress_framework_spec.spl` | `std.common.compress` |
| 8 | module present | `test/unit/lib/common/compress_utilities_spec.spl` | `std.common.compress.utilities` |
| 7 | module present | `test/unit/browser/script/navigator_api_spec.spl` | `std.gc_async_mut.gpu.browser_engine.script.navigator_api` |
| 7 | module absent | `test/unit/lib/blink/flex_spec.spl` | `std.blink.layout.flex` |
| 7 | mixed | `test/unit/lib/common/wine_process_entrypoint_startup_fault_spec.spl` | `common.wine_process_entrypoint_startup_fault`, `common.wine_process_session`, `common.wine_seh_frame` |
| 7 | module absent | `test/system/app/simpleos/feature/simpleos_proton_substrate_spec.spl` | `common.wine_proton_gate`, `common.wine_proton_runtime` |
| 7 | module absent | `test/unit/lib/gc_async_mut/gpu/engine2d/rendering_parity_adapter_spec.spl` | `std.gc_async_mut.gpu.browser_engine.rendering_parity_adapter`, `std.gc_async_mut.gpu.engine2d.rendering_parity_adapter` |
| 7 | module absent | `test/system/feature/usage/llvm_backend_spec.spl` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| 7 | module absent | `test/feature/usage/llvm_backend_spec.spl` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| 7 | mixed | `test/integration/rendering/backend_screenshot_compare_spec.spl` | `common.ui.glass_test_page`, `os.compositor.screenshot_compare`, `std.gc_async_mut.gpu.browser_engine.backend_screenshot_capture` |
| 6 | module absent | `test/unit/app/ui/async_ui_spec.spl` | `common.ui.async_state` |
| 6 | module absent | `test/unit/hardware/rv32imac/rv32_compressed_spec.spl` | `hardware.rv32imac.core.rv32_compressed`, `hardware.rv32imac.core.rv32_decode` |
| 6 | module absent | `test/unit/hardware/rv64gc/rv64_fp_compare_d_spec.spl` | `hardware.rv64gc.ext.rv64_double` |
| 6 | module absent | `test/unit/hardware/rv64gc/rv64_fp_compare_s_spec.spl` | `hardware.rv64gc.ext.rv64_float` |
| 6 | mixed | `test/unit/lib/blink/style_cascade_spec.spl` | `std.blink.dom.node`, `std.blink.entity.computed_style`, `std.blink.style.cascade` |
| 6 | module absent | `test/unit/lib/blink/input_event_spec.spl` | `std.blink.input.event` |
| 6 | module present | `test/unit/lib/common/proton_runtime_subsystems_spec.spl` | `common.proton_runtime_subsystems` |
| 6 | module present | `test/unit/lib/common/wine_vm_adapter_spec.spl` | `common.wine_vm_adapter` |
| 6 | module present | `test/unit/lib/common/wine_process_session_spec.spl` | `common.wine_process_session` |
| 6 | module absent | `test/unit/lib/common/wine_proton_gate_spec.spl` | `common.wine_proton_gate` |
| 6 | module absent | `test/unit/lib/common/wine_proton_runtime_spec.spl` | `common.wine_proton_gate`, `common.wine_proton_runtime` |
| 6 | module absent | `test/unit/lib/common/wine_thread_adapter_spec.spl` | `common.wine_thread_adapter` |
| 6 | module absent | `test/system/feature/usage/llvm_backend_aarch64_spec.spl` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| 6 | module absent | `test/system/feature/usage/llvm_backend_i686_spec.spl` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| 6 | module absent | `test/feature/usage/llvm_backend_aarch64_spec.spl` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| 6 | module absent | `test/feature/usage/llvm_backend_i686_spec.spl` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| 6 | mixed | `test/integration/rendering/simd_parity_spec.spl` | `compiler.backend.native.x86_64_simd`, `compiler.mir_opt.optimizer_manifest` |
| 6 | module present | `test/system/os/qemu/os/harden/cap_exec_gate_spec.spl` | `os.qemu_systest_contract` |
| 6 | module present | `test/system/os/qemu/os/harden/hardened_malloc_spec.spl` | `os.qemu_systest_contract` |
| 6 | module present | `test/system/os/qemu/os/harden/pie_ssp_relro_preset_spec.spl` | `os.qemu_systest_contract` |
| 5 | module absent | `test/unit/doc/riscv_fpga_bug_tracking_spec.spl` | `doc.bugs.riscv_fpga_bug_convention` |
| 5 | module absent | `test/unit/hardware/rv64gc/rv64_alu_imm_spec.spl` | `hardware.rv64gc.core.rv64_decode`, `hardware.rv64gc.core.rv64_execute` |
| 5 | module absent | `test/integration/hardware/rv64gc/rv64_compliance_spec.spl` | `hardware.rv64gc.core.rv64_execute`, `hardware.rv64gc.ext.rv64_atomics`, `hardware.rv64gc.ext.rv64_muldiv` |
| 5 | module absent | `test/integration/hardware/rv32imac/rv32_compliance_spec.spl` | `hardware.riscv_common.pkg.riscv_types_pkg`, `hardware.rv64gc.ext.rv64_atomics` |
| 5 | module absent | `test/unit/hardware/rv64gc/rv64_fp_arith_d_spec.spl` | `hardware.rv64gc.ext.rv64_double` |
| 5 | module absent | `test/unit/hardware/rv64gc/rv64_fp_arith_s_spec.spl` | `hardware.rv64gc.ext.rv64_float` |
| 5 | module absent | `test/unit/lib/blink/paint_chunk_spec.spl` | `std.blink.entity.paint_chunk` |
| 5 | module absent | `test/unit/lib/blink/scroll_manager_spec.spl` | `std.blink.scroll.manager` |
| 5 | module absent | `test/unit/lib/cc/tile_spec.spl` | `std.lib.cc.entity.tile` |
| 5 | module absent | `test/unit/lib/common/wine_rtl_string_spec.spl` | `common.wine_rtl_string` |
| 5 | module absent | `test/unit/lib/common/wine_vm_gate_spec.spl` | `common.wine_vm_gate` |
| 5 | module absent | `test/unit/lib/common/wine_x86_64_decode_spec.spl` | `common.wine_x86_64_decode` |
| 5 | module present | `test/unit/lib/engine/build_pipeline_spec.spl` | `std.nogc_sync_mut.engine.build.build_config`, `std.nogc_sync_mut.engine.build.build_pipeline` |
| 5 | module absent | `test/unit/lib/math/field/fe_p256_full_spec.spl` | `std.common.math.field.fe_p256` |
| 5 | module absent | `test/integration/baremetal/baremetal_build_spec.spl` | `app.build.baremetal` |
| 5 | module absent | `test/system/feature/usage/llvm_backend_arm32_spec.spl` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| 5 | module absent | `test/system/feature/usage/llvm_backend_riscv32_spec.spl` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| 5 | module absent | `test/system/feature/usage/llvm_backend_riscv64_spec.spl` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| 5 | module absent | `test/feature/usage/llvm_backend_arm32_spec.spl` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| 5 | module absent | `test/feature/usage/llvm_backend_riscv32_spec.spl` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| 5 | module absent | `test/feature/usage/llvm_backend_riscv64_spec.spl` | `compiler.backend.llvm_ir_builder`, `compiler.backend.llvm_target`, `compiler.backend.llvm_type_mapper` |
| 4 | module present | `test/unit/app/ui/capability_policy_spec.spl` | `std.common.ui.capability`, `std.common.ui.capability_policy` |
| 4 | module absent | `test/unit/doc/de10nano_quartus_setup_spec.spl` | `doc.fpga.de10nano_quartus_setup` |
| 4 | module absent | `test/system/hardware/rv32imac_spec.spl` | `hardware.riscv_common.core.riscv_compressed`, `hardware.riscv_common.pkg.riscv_types_pkg` |
| 4 | module absent | `test/system/rv32imac_spec.spl` | `hardware.riscv_common.core.riscv_compressed`, `hardware.riscv_common.pkg.riscv_types_pkg` |
| 4 | module absent | `test/unit/hardware/rv64gc/rv64_fp_fused_d_spec.spl` | `hardware.rv64gc.ext.rv64_double` |
| 4 | module absent | `test/unit/hardware/rv64gc/rv64_fp_fused_s_spec.spl` | `hardware.rv64gc.ext.rv64_float` |
| 4 | module absent | `test/unit/lib/blink/block_flow_spec.spl` | `std.blink.layout.block_flow` |
| 4 | module absent | `test/unit/lib/blink/navigation_controller_spec.spl` | `std.blink.navigation.controller` |
| 4 | module present | `test/unit/lib/common/wine_arbitrary_pe_spec.spl` | `common.wine_hello_exe` |
| 4 | module present | `test/unit/lib/crypto/crypto_reference_spec.spl` | `std.crypto.legacy_hash`, `std.crypto.pbkdf2` |
| 4 | module absent | `test/unit/lib/gc_async_mut/gpu/browser_engine/rendering_parity_adapter_spec.spl` | `std.gc_async_mut.gpu.browser_engine.rendering_parity_adapter` |
| 4 | module absent | `test/unit/lib/math/field/fe25519_spec.spl` | `std.common.math.field.fe25519` |
| 4 | module present | `test/unit/os/apps/terminal/terminal_spec.spl` | `os.apps.terminal.terminal` |
| 4 | module present | `test/unit/os/compositor/shared_mdi_framebuffer_scene_spec.spl` | `os.compositor.shared_mdi_framebuffer_scene` |
| 4 | module present | `test/system/feature/app/t32_tools/t32_mcp_tools_spec.spl` | `app.mcp_t32.action_tools` |
| 3 | module absent | `test/unit/compiler/backend/layout_scanner_spec.spl` | `app.build` |
| 3 | module absent | `test/unit/compiler/mdsoc/pipeline_integration_spec.spl` | `compiler.mdsoc.feature.cache.cache_port` |
| 3 | module absent | `test/unit/hardware/rv64gc/rv64_atomics_spec.spl` | `hardware.rv64gc.ext.rv64_atomics` |
| 3 | module absent | `test/unit/hardware/rv64gc/rv64_fp_sign_s_spec.spl` | `hardware.rv64gc.ext.rv64_float` |
| 3 | module present | `test/unit/lib/blink/css_selector_spec.spl` | `std.blink.dom.node` |
| 3 | module absent | `test/unit/lib/blink/navigation_fetch_spec.spl` | `std.blink.navigation.controller`, `std.blink.network.fetch` |
| 3 | module absent | `test/unit/lib/blink/paint_artifact_spec.spl` | `std.blink.entity.paint_artifact` |
| 3 | module absent | `test/unit/lib/blink/url/url_parser_spec.spl` | `std.blink.url.url_parser` |
| 3 | module absent | `test/unit/lib/cc/layer_base_spec.spl` | `std.lib.cc.entity.layer_base` |
| 3 | module absent | `test/unit/lib/cc/property_tree_spec.spl` | `std.lib.cc.entity.property_tree` |
| 3 | module absent | `test/unit/lib/cc/tile_manager_spec.spl` | `std.cc.entity.tile`, `std.cc.feature.raster_buffer_provider` |
| 3 | module present | `test/unit/lib/common/wine_hello_fixture_spec.spl` | `common.wine_hello_exe`, `common.wine_hello_fixture` |
| 3 | mixed | `test/system/app/simpleos/feature/simpleos_wine_process_entrypoint_startup_fault_spec.spl` | `common.wine_process_entrypoint_startup_fault`, `common.wine_process_session` |
| 3 | module present | `test/unit/lib/common/wine_process_session_import_descriptor_table_spec.spl` | `common.wine_process_session` |
| 3 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl` | `common.wine_process_session` |
| 3 | module absent | `test/system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl` | `common.wine_x86_64_decode` |
| 3 | module absent | `test/unit/lib/common/units/generators/world_units_importers_spec.spl` | `std.common.units.generators.world_units_importers` |
| 3 | module absent | `test/unit/lib/debug/remote/t32_ffi/t32_version_detect_spec.spl` | `std.debug.remote.t32_ffi.t32_execute`, `std.debug.remote.t32_ffi.t32_notify`, `std.debug.remote.t32_ffi.t32_version_detect` |
| 3 | module present | `test/unit/lib/engine/units_spec.spl` | `std.common.engine.units` |
| 3 | module present | `test/unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.spl` | `lib.hardware.fpga_k26.k26_soc_top` |
| 3 | module present | `test/unit/lib/hardware/fpga_linux/synthesis_wrapper_vexriscv_spec.spl` | `lib.hardware.fpga_linux.synthesis_wrapper` |
| 3 | module present | `test/unit/lib/http_server/rate_limit_spec.spl` | `std.http_server.rate_limit` |
| 3 | module present | `test/unit/lib/http_server/request_validation_spec.spl` | `std.http_server.request_validation` |
| 3 | module absent | `test/unit/lib/mcp/lazy_loading_spec.spl` | `mcp_lib.lazy_registry` |
| 3 | module absent | `test/unit/lib/unit/unit_composite_spec.spl` | `unit.energy`, `unit.velocity` |
| 3 | mixed | `test/unit/os/compositor/engine2d_render_evidence_spec.spl` | `os.drivers.framebuffer.ramfb`, `os.kernel.arch.x86.render_capture_ack` |
| 3 | module absent | `test/unit/std/parser/treesitter_node_spec.spl` | `std.parser.treesitter_node` |
| 3 | module absent | `test/integration/rv32_multi_backend_boot_spec.spl` | `test.helpers.riscv_encode`, `timing.hybrid_sim`, `timing.types` |
| 3 | module present | `test/unit/lib/http_server/csrf_spec.spl` | `std.http_server.csrf` |
| 2 | module present | `test/unit/app/ui.chromium/css_spec.spl` | `std.gc_async_mut.gpu.browser_engine.css` |
| 2 | module present | `test/unit/browser/script/console_api_spec.spl` | `std.gc_async_mut.gpu.browser_engine.script.console_api`, `std.gc_async_mut.gpu.browser_engine.webgpu_context` |
| 2 | module present | `test/unit/browser_engine/html_tree_builder_spec.spl` | `std.gc_async_mut.gpu.browser_engine.dom_accessors` |
| 2 | module absent | `test/unit/compiler/ffi_gen/backend_gating_spec.spl` | `compiler.tools.ffi_gen.main` |
| 2 | module present | `test/unit/compiler/mir_opt/collection_opt_spec.spl` | `compiler.mir.mir_types`, `compiler.mir_opt.mir_opt.collection_opt` |
| 2 | module absent | `test/unit/hardware/rv64gc/rv64_compressed_spec.spl` | `hardware.rv64gc.core.rv64_compressed` |
| 2 | module absent | `test/integration/hardware/rv64gc/rv64_core_smoke_spec.spl` | `hardware.rv64gc.core.rv64_execute` |
| 2 | module absent | `test/integration/os/rv64_boot_spec.spl` | `hardware.rv64gc.core.rv64_execute` |
| 2 | module absent | `test/unit/hardware/rv64gc/rv64_atomics_ordering_spec.spl` | `hardware.rv64gc.ext.rv64_atomics` |
| 2 | module absent | `test/unit/lib/blink/computed_style_spec.spl` | `std.blink.entity.computed_style` |
| 2 | module absent | `test/unit/lib/blink/html_tokenizer_spec.spl` | `std.blink.html_parser` |
| 2 | module absent | `test/unit/lib/blink/html_tree_builder_spec.spl` | `std.blink.html_parser`, `std.blink.html_parser.tree_builder` |
| 2 | module absent | `test/unit/lib/blink/paint_controller_spec.spl` | `std.blink.entity.paint_artifact`, `std.blink.feature.paint.paint_controller` |
| 2 | module absent | `test/unit/lib/cc/layer_tree_host_spec.spl` | `std.cc.entity.layer_tree_host` |
| 2 | module absent | `test/unit/lib/cc/picture_layer_impl_spec.spl` | `std.cc.feature.picture_layer_impl`, `std.cc.feature.raster_source` |
| 2 | module present | `test/unit/lib/common/wine_hello_exe_spec.spl` | `common.wine_hello_exe` |
| 2 | module absent | `test/unit/lib/common/wine_precondition_manifest_spec.spl` | `common.wine_precondition_manifest` |
| 2 | module absent | `test/unit/lib/common/wine_seh_frame_spec.spl` | `common.wine_seh_frame` |
| 2 | module absent | `test/system/app/simpleos/feature/simpleos_wine_seh_frame_spec.spl` | `common.wine_seh_frame` |
| 2 | module present | `test/unit/lib/common/wine_process_session_full_image_handoff_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/unit/lib/common/wine_process_session_import_loader_transaction_rejection_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_import_loader_transaction_rejection_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/unit/lib/common/wine_process_session_known_console_dispatch_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/system/app/simpleos/feature/simpleos_wine_known_console_dispatch_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/unit/lib/common/wine_process_session_known_console_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/system/app/simpleos/feature/simpleos_wine_known_console_execution_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/unit/lib/common/wine_process_session_loader_runtime_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_loader_runtime_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/unit/lib/common/wine_process_session_mapped_image_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/unit/lib/common/wine_process_session_module_loader_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_module_loader_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/unit/lib/common/wine_process_session_thunk_load_bind_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/unit/lib/common/wine_process_session_thunk_apply_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_thunk_apply_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/unit/lib/common/wine_process_session_tls_dispatch_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/unit/lib/common/wine_process_session_vma_relocation_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_vma_relocation_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/unit/lib/common/wine_process_session_vma_thunk_write_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_vma_thunk_write_spec.spl` | `common.wine_process_session` |
| 2 | module present | `test/unit/lib/common/immut/combinators_spec.spl` | `lib.combinators.pipeline` |
| 2 | module present | `test/unit/lib/immut/combinators_spec.spl` | `std.combinators.pipeline` |
| 2 | module absent | `test/unit/lib/common/units/engine/unit_expr_spec.spl` | `std.common.units.engine.unit_expr` |
| 2 | module present | `test/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl` | `std.hardware.rv64gc_rtl.core` |
| 2 | module present | `test/unit/lib/http_server/security_headers_spec.spl` | `std.http_server.security_headers` |
| 2 | module present | `test/unit/lib/nogc_sync_mut/engine/render/shader_compile_spec.spl` | `std.nogc_sync_mut.engine.render.shader_compile` |
| 2 | module absent | `test/unit/lib/std/game_engine/effects_spec.spl` | `std.game_engine.effects` |
| 2 | module absent | `test/unit/lib/unit/unit_literal_postfix_spec.spl` | `unit.temperature`, `unit.velocity` |
| 2 | module absent | `test/integration/rendering/effect_engine_compare_spec.spl` | `common.ui.glass_test_page` |
| 2 | mixed | `test/integration/rendering/glass_pipeline_screenshot_spec.spl` | `common.ui.glass_test_page`, `os.compositor.screenshot_compare` |
| 2 | module absent | `test/integration/rendering/glass_render_e2e_spec.spl` | `common.ui.glass_test_page` |
| 2 | module present | `test/system/feature/web_platform/css/wpt_scorecard_spec.spl` | `std.gc_async_mut.gpu.browser_engine.paint`, `std.gc_async_mut.gpu.browser_engine.style.animation` |
| 2 | module present | `test/feature/web_platform/css/wpt_scorecard_spec.spl` | `std.gc_async_mut.gpu.browser_engine.paint`, `std.gc_async_mut.gpu.browser_engine.style.animation` |
| 2 | module present | `test/system/feature/web_platform/webgpu/webgpu_facade_spec.spl` | `std.gc_async_mut.gpu.browser_engine.mod` |
| 2 | module present | `test/feature/web_platform/webgpu/webgpu_facade_spec.spl` | `std.gc_async_mut.gpu.browser_engine.mod` |
| 2 | module present | `test/system/helpers/text_helpers_p1_spec.spl` | `common.text_advanced` |
| 2 | module present | `test/system/text_helpers_p1_spec.spl` | `common.text_advanced` |
| 2 | module absent | `test/system/lib/database/postgres_mimic_server_spec.spl` | `std.database.deployment` |
| 1 | module absent | `test/unit/app/lifecycle_spec.spl` | `nogc_sync_mut.src.app.runner` |
| 1 | module present | `test/unit/app/cli/cli_os_spec.spl` | `app.cli.main` |
| 1 | module absent | `test/unit/app/test_daemon/test_daemon_session_config_spec.spl` | `test_config` |
| 1 | module present | `test/unit/app/tooling/test_result_wrapper_authored_count_spec.spl` | `std.test_runner.test_result_wrapper` |
| 1 | module present | `test/unit/app/ui.chromium/text_metrics_spec.spl` | `std.gc_async_mut.gpu.browser_engine.text_painter` |
| 1 | module absent | `test/unit/app/ui/async_default_api_spec.spl` | `common.ui` |
| 1 | module present | `test/unit/app/ui/shared_wm_entrypoints_spec.spl` | `os.compositor.host_compositor_entry` |
| 1 | module absent | `test/unit/app/ui/unified_app_spec.spl` | `common.ui.app` |
| 1 | module absent | `test/system/gui/unified_app_spec.spl` | `common.ui.app` |
| 1 | module present | `test/unit/browser_engine/anonymous_block_spec.spl` | `std.gc_async_mut.gpu.browser_engine.dom_accessors` |
| 1 | module present | `test/unit/browser_engine/ifc_linebox_spec.spl` | `std.gc_async_mut.gpu.browser_engine.layout` |
| 1 | module present | `test/unit/browser_engine/layout_text_node_spec.spl` | `std.gc_async_mut.gpu.browser_engine.layout_core` |
| 1 | module present | `test/unit/browser_engine/table_layout_spec.spl` | `std.gc_async_mut.gpu.browser_engine.layout` |
| 1 | module absent | `test/unit/compiler/diagnostic_formatter_contract_spec.spl` | `std.diagnostics.formatters` |
| 1 | module absent | `test/unit/compiler/wasm_codegen_spec.spl` | `compiler.backend.wasm_type_mapper` |
| 1 | module absent | `test/system/feature/usage/wasm_compile_spec.spl` | `compiler.backend.wasm_type_mapper` |
| 1 | module absent | `test/feature/usage/wasm_compile_spec.spl` | `compiler.backend.wasm_type_mapper` |
| 1 | module absent | `test/unit/compiler/module_resolver/type_domain_resolver_spec.spl` | `compiler.module_resolver.resolution` |
| 1 | module present | `test/unit/compiler/semantics/flat_imported_method_resolution_spec.spl` | `compiler.semantics.resolve` |
| 1 | module present | `test/unit/lib/blink/dom_node_spec.spl` | `std.blink.dom.node` |
| 1 | module absent | `test/unit/lib/blink/document_spec.spl` | `std.blink.dom.document` |
| 1 | module absent | `test/unit/lib/content/web_contents_spec.spl` | `std.blink.entity.paint_artifact` |
| 1 | module present | `test/unit/lib/common/proton_real_exec_spec.spl` | `common.proton_runtime_subsystems` |
| 1 | module present | `test/unit/lib/common/proton_session_spec.spl` | `common.proton_runtime_subsystems` |
| 1 | module present | `test/unit/lib/common/wine_image_vm_map_spec.spl` | `common.wine_vm_adapter` |
| 1 | module present | `test/unit/lib/common/wine_kernel32_global_memory_spec.spl` | `common.wine_vm_adapter` |
| 1 | module present | `test/unit/lib/common/wine_kernel32_heap_spec.spl` | `common.wine_vm_adapter` |
| 1 | module present | `test/unit/lib/common/wine_kernel32_local_memory_spec.spl` | `common.wine_vm_adapter` |
| 1 | module present | `test/unit/lib/common/wine_kernel32_virtual_memory_spec.spl` | `common.wine_vm_adapter` |
| 1 | module present | `test/unit/lib/common/wine_nt_heap_spec.spl` | `common.wine_vm_adapter` |
| 1 | module present | `test/unit/lib/common/wine_nt_virtual_memory_spec.spl` | `common.wine_vm_adapter` |
| 1 | module present | `test/unit/lib/common/wine_ntdll_bridge_spec.spl` | `common.wine_vm_adapter` |
| 1 | module present | `test/unit/lib/common/wine_process_session_cpu_preflight_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_cpu_preflight_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/unit/lib/common/wine_process_session_first_import_module_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_first_import_module_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/unit/lib/common/wine_process_session_import_descriptor_vma_vm_write_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_import_descriptor_vma_vm_write_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/unit/lib/common/wine_process_session_import_entrypoint_handoff_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_import_entrypoint_handoff_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/unit/lib/common/wine_process_session_import_entrypoint_handoff_vm_write_failure_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/unit/lib/common/wine_process_session_import_entrypoint_handoff_vm_write_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_import_entrypoint_handoff_vm_write_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/unit/lib/common/wine_process_session_import_transaction_rollback_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/unit/lib/common/wine_process_session_import_transaction_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/unit/lib/common/wine_process_session_import_transaction_vm_write_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_import_loader_transaction_vm_write_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/unit/lib/common/wine_process_session_import_patch_records_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_import_patch_records_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/unit/lib/common/wine_process_session_import_resolution_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_import_resolution_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/unit/lib/common/wine_process_session_import_vma_patch_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/unit/lib/common/wine_process_session_load_bind_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_load_bind_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/unit/lib/common/wine_process_session_loader_state_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/unit/lib/common/wine_process_session_thunk_records_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/system/app/simpleos/feature/simpleos_wine_process_thunk_records_spec.spl` | `common.wine_process_session` |
| 1 | module present | `test/unit/lib/common/immut/integration_spec.spl` | `lib.combinators.pipeline` |
| 1 | module present | `test/unit/lib/immut/integration_spec.spl` | `std.combinators.pipeline` |
| 1 | module present | `test/unit/lib/common/win_fs/window_record_spec.spl` | `lib.common.win_fs.window_record` |
| 1 | module present | `test/unit/lib/content/render_widget_host_view_spec.spl` | `std.content.feature.render_widget_host_view` |
| 1 | module present | `test/unit/lib/crypto/chacha20_spec.spl` | `std.crypto.chacha20` |
| 1 | module present | `test/unit/lib/crypto/poly1305_spec.spl` | `std.crypto.poly1305` |
| 1 | module present | `test/unit/lib/crypto/sha2_nist_vectors_spec.spl` | `std.crypto.sha512` |
| 1 | module present | `test/unit/lib/engine/device_spec.spl` | `std.common.gpu.device` |
| 1 | module present | `test/unit/lib/gpu/graphics_context_spec.spl` | `std.common.gpu.device` |
| 1 | module present | `test/unit/lib/engine/ids_spec.spl` | `std.common.engine.ids` |
| 1 | module present | `test/unit/lib/gpu/engine2d/generated_kernel_args_spec.spl` | `std.gc_async_mut.gpu.engine2d.generated_kernel_dispatch` |
| 1 | module present | `test/unit/lib/gpu/engine2d/helpers_text_cache_spec.spl` | `std.gpu.engine2d.helpers_text` |
| 1 | module absent | `test/unit/lib/math/field/fe_p256_skeleton_spec.spl` | `std.common.math.field.fe_p256` |
| 1 | module present | `test/unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.spl` | `std.nogc_sync_mut.db.dbfs_engine.raw_nvme_arena` |
| 1 | module absent | `test/system/e2e/unit_system_integration_spec.spl` | `unit.velocity` |
| 1 | module absent | `test/system/unit_system_integration_spec.spl` | `unit.velocity` |
| 1 | module absent | `test/unit/lib/unit/unit_raw_warning_spec.spl` | `unit.length` |
| 1 | module present | `test/unit/os/__tmp_adapter_probe_spec.spl` | `os.kernel.memory.memory_leveling_device_adapters` |
| 1 | module present | `test/unit/os/apps/browser_demo_render_spec.spl` | `os.apps.browser_demo.browser_demo` |
| 1 | module present | `test/unit/os/compositor/wm_action_applier_spec.spl` | `os.compositor.wm_action_applier` |
| 1 | module present | `test/unit/os/desktop/wm_background_motion_provider_spec.spl` | `os.compositor.shared_mdi_framebuffer_scene` |
| 1 | module absent | `test/unit/os/drivers/audio/hda_pcm_pack_spec.spl` | `std.common.audio.pcm_i16` |
| 1 | module present | `test/unit/os/kernel/arch/syscall_dispatch_spec.spl` | `std.spec` |
| 1 | module absent | `test/unit/os/qemu/arm64_wm_shared_mdi_contract_spec.spl` | `examples.simple_os.arch.arm64.wm_shared_mdi_contract` |
| 1 | module present | `test/unit/os/shell/awk_spec.spl` | `os.tools.shell.awk.awk_tool` |
| 1 | module present | `test/unit/os/shell/shell_script_spec.spl` | `os.apps.shell.shell_expand` |
| 1 | module present | `test/integration/app/simple_process_manager/spm_service_spec.spl` | `lib.common.win_fs.window_record` |
| 1 | module absent | `test/integration/compiler/llvm_compiled_proof_spec.spl` | `compiler.backend.llvm_target` |
| 1 | module absent | `test/integration/compiler/llvm_text_bitcode_debug_spec.spl` | `compiler.backend.llvm_target` |
| 1 | module absent | `test/integration/hardware/rv32gc/rv32_linux_platform_contract_spec.spl` | `hardware.rv32gc.top.rv32_soc` |
| 1 | module absent | `test/integration/hardware/rv32imac/rv32_hello_world_spec.spl` | `hardware.rv32gc.periph.rv32_uart` |
| 1 | module present | `test/integration/net/http_content_encoding_spec.spl` | `std.nogc_sync_mut.compression.zlib` |
| 1 | module present | `test/system/app/browser/feature/browser_stop_partial_focus_spec.spl` | `std.gc_async_mut.gpu.browser_engine.dom_accessors` |
| 1 | module absent | `test/system/feature/app/t32_tools/t32_mcp_spec.spl` | `app.mcp_t32.protocol` |
| 1 | module absent | `test/system/feature/language/modules_spec.spl` | `self.tls` |
| 1 | module present | `test/feature/web_platform/css/animations_wpt_spec.spl` | `std.gc_async_mut.gpu.browser_engine.style.animation` |
| 1 | module present | `test/feature/web_platform/css/object_fit_wpt_spec.spl` | `std.gc_async_mut.gpu.browser_engine.paint` |
| 1 | module present | `test/system/feature/web_platform/html/address_element_rendering_spec.spl` | `std.gc_async_mut.gpu.browser_engine.dom_accessors` |
| 1 | module present | `test/system/feature/web_platform/webgpu/webgpu_commands_spec.spl` | `std.gc_async_mut.gpu.browser_engine.webgpu_resources` |
| 1 | module present | `test/feature/web_platform/webgpu/webgpu_commands_spec.spl` | `std.gc_async_mut.gpu.browser_engine.webgpu_resources` |
| 1 | module absent | `test/system/gui/command_history_spec.spl` | `std.common.command.command` |
| 1 | module absent | `test/system/command_history_spec.spl` | `std.common.command.command` |
| 1 | module present | `test/system/os/simpleos_desktop_framebuffer_spec.spl` | `os.compositor.qemu_capture` |
| 1 | module present | `test/system/os/simpleos_desktop_with_apps_framebuffer_spec.spl` | `os.compositor.qemu_capture` |
| 1 | module present | `test/system/simpleos_desktop_framebuffer_spec.spl` | `os.compositor.qemu_capture` |
| 1 | module present | `test/system/simpleos_desktop_with_apps_framebuffer_spec.spl` | `os.compositor.qemu_capture` |
| 1 | module absent | `test/system/os_rt_rsa_pss_verify_spec.spl` | `std.nogc_sync_mut.io.signature_ffi` |
| 1 | module absent | `test/unit/compiler/frontend/required_comment_parse_spec.spl` | `compiler.core.ast_expr` |

## 7. Per-name detail for the module-present cases

These are the ones where a file exists and an API surface was specified but never written
(or was renamed without updating the spec).

**`test/unit/browser/script/canvas_api_spec.spl`** (344) <- `std.gc_async_mut.gpu.browser_engine.script.canvas_api`, `std.gc_async_mut.gpu.browser_engine.webgpu_resources`

> `CANVAS_WEBGL_ACTIVE_TEXTURE`, `CANVAS_WEBGL_ALIASED_LINE_WIDTH_RANGE`, `CANVAS_WEBGL_ALWAYS`, `CANVAS_WEBGL_ARRAY_BUFFER`, `CANVAS_WEBGL_BACK`, `CANVAS_WEBGL_BLEND_COLOR`, `CANVAS_WEBGL_BLEND_DST_ALPHA`, `CANVAS_WEBGL_BLEND_DST_RGB`, `CANVAS_WEBGL_BLEND_EQUATION_ALPHA`, `CANVAS_WEBGL_BLEND_EQUATION_RGB`, `CANVAS_WEBGL_BLEND_SRC_ALPHA`, `CANVAS_WEBGL_BLEND_SRC_RGB`, `CANVAS_WEBGL_BUFFER_SIZE`, `CANVAS_WEBGL_BUFFER_USAGE`, `CANVAS_WEBGL_BYTE`, `CANVAS_WEBGL_CLAMP_TO_EDGE`, `CANVAS_WEBGL_COLOR_ATTACHMENT0`, `CANVAS_WEBGL_COLOR_BUFFER_BIT`, `CANVAS_WEBGL_COLOR_CLEAR_VALUE`, `CANVAS_WEBGL_COLOR_WRITEMASK`, `CANVAS_WEBGL_COMPRESSED_TEXTURE_FORMATS`, `CANVAS_WEBGL_CONTEXT_LOST_WEBGL`, `CANVAS_WEBGL_CULL_FACE_MODE`, `CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB`, `CANVAS_WEBGL_CW`, `CANVAS_WEBGL_DELETE_STATUS`, `CANVAS_WEBGL_DEPTH_ATTACHMENT`, `CANVAS_WEBGL_DEPTH_CLEAR_VALUE`, `CANVAS_WEBGL_DEPTH_COMPONENT16`, `CANVAS_WEBGL_DEPTH_FUNC`, `CANVAS_WEBGL_DEPTH_RANGE`, `CANVAS_WEBGL_DEPTH_WRITEMASK`, `CANVAS_WEBGL_DITHER`, `CANVAS_WEBGL_DRAW_BUFFER0`, `CANVAS_WEBGL_ELEMENT_ARRAY_BUFFER`, `CANVAS_WEBGL_FLOAT`, `CANVAS_WEBGL_FLOAT_MAT2`, `CANVAS_WEBGL_FLOAT_MAT3`, `CANVAS_WEBGL_FLOAT_MAT4`, `CANVAS_WEBGL_FLOAT_VEC2`, `CANVAS_WEBGL_FLOAT_VEC3`, `CANVAS_WEBGL_FLOAT_VEC4`, `CANVAS_WEBGL_FRAGMENT_SHADER`, `CANVAS_WEBGL_FRAMEBUFFER`, `CANVAS_WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_NAME`, `CANVAS_WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_TYPE`, `CANVAS_WEBGL_FRAMEBUFFER_COMPLETE`, `CANVAS_WEBGL_FRAMEBUFFER_INCOMPLETE_MISSING_ATTACHMENT`, `CANVAS_WEBGL_FRONT`, `CANVAS_WEBGL_FRONT_AND_BACK`, `CANVAS_WEBGL_FRONT_FACE`, `CANVAS_WEBGL_FUNC_ADD`, `CANVAS_WEBGL_FUNC_SUBTRACT`, `CANVAS_WEBGL_GENERATE_MIPMAP_HINT`, `CANVAS_WEBGL_HIGH_FLOAT`, `CANVAS_WEBGL_INT`, `CANVAS_WEBGL_INT_VEC2`, `CANVAS_WEBGL_INT_VEC3`, `CANVAS_WEBGL_INT_VEC4`, `CANVAS_WEBGL_INVALID_ENUM`, `CANVAS_WEBGL_KEEP`, `CANVAS_WEBGL_LEQUAL`, `CANVAS_WEBGL_LINEAR`, `CANVAS_WEBGL_LINEAR_MIPMAP_LINEAR`, `CANVAS_WEBGL_LINES`, `CANVAS_WEBGL_LINE_LOOP`, `CANVAS_WEBGL_LINE_STRIP`, `CANVAS_WEBGL_LINE_WIDTH`, `CANVAS_WEBGL_MAX_DRAW_BUFFERS`, `CANVAS_WEBGL_MAX_TEXTURE_SIZE`, `CANVAS_WEBGL_MAX_VIEWPORT_DIMS`, `CANVAS_WEBGL_MEDIUM_INT`, `CANVAS_WEBGL_MIRRORED_REPEAT`, `CANVAS_WEBGL_NICEST`, `CANVAS_WEBGL_NONE`, `CANVAS_WEBGL_NO_ERROR`, `CANVAS_WEBGL_ONE`, `CANVAS_WEBGL_ONE_MINUS_SRC_ALPHA`, `CANVAS_WEBGL_PACK_ALIGNMENT`, `CANVAS_WEBGL_POLYGON_OFFSET_FACTOR`, `CANVAS_WEBGL_POLYGON_OFFSET_FILL`, `CANVAS_WEBGL_POLYGON_OFFSET_UNITS`, `CANVAS_WEBGL_READ_BUFFER`, `CANVAS_WEBGL_RENDERBUFFER`, `CANVAS_WEBGL_RENDERBUFFER_HEIGHT`, `CANVAS_WEBGL_RENDERBUFFER_INTERNAL_FORMAT`, `CANVAS_WEBGL_RENDERBUFFER_WIDTH`, `CANVAS_WEBGL_REPLACE`, `CANVAS_WEBGL_RGB`, `CANVAS_WEBGL_RGBA`, `CANVAS_WEBGL_RGBA4`, `CANVAS_WEBGL_SAMPLER_2D`, `CANVAS_WEBGL_SAMPLER_BINDING`, `CANVAS_WEBGL_SAMPLER_CUBE`, `CANVAS_WEBGL_SAMPLE_COVERAGE`, `CANVAS_WEBGL_SAMPLE_COVERAGE_INVERT`, `CANVAS_WEBGL_SAMPLE_COVERAGE_VALUE`, `CANVAS_WEBGL_SCISSOR_BOX`, `CANVAS_WEBGL_SHADER_TYPE`, `CANVAS_WEBGL_SHORT`, `CANVAS_WEBGL_SRC_ALPHA`, `CANVAS_WEBGL_STATIC_DRAW`, `CANVAS_WEBGL_STENCIL_BACK_FAIL`, `CANVAS_WEBGL_STENCIL_BACK_FUNC`, `CANVAS_WEBGL_STENCIL_BACK_PASS_DEPTH_FAIL`, `CANVAS_WEBGL_STENCIL_BACK_PASS_DEPTH_PASS`, `CANVAS_WEBGL_STENCIL_BACK_REF`, `CANVAS_WEBGL_STENCIL_BACK_VALUE_MASK`, `CANVAS_WEBGL_STENCIL_BACK_WRITEMASK`, `CANVAS_WEBGL_STENCIL_FAIL`, `CANVAS_WEBGL_STENCIL_FUNC`, `CANVAS_WEBGL_STENCIL_PASS_DEPTH_FAIL`, `CANVAS_WEBGL_STENCIL_PASS_DEPTH_PASS`, `CANVAS_WEBGL_STENCIL_REF`, `CANVAS_WEBGL_STENCIL_VALUE_MASK`, `CANVAS_WEBGL_STENCIL_WRITEMASK`, `CANVAS_WEBGL_TEXTURE`, `CANVAS_WEBGL_TEXTURE0`, `CANVAS_WEBGL_TEXTURE_2D`, `CANVAS_WEBGL_TEXTURE_BINDING_2D`, `CANVAS_WEBGL_TEXTURE_BINDING_CUBE_MAP`, `CANVAS_WEBGL_TEXTURE_CUBE_MAP`, `CANVAS_WEBGL_TEXTURE_CUBE_MAP_POSITIVE_X`, `CANVAS_WEBGL_TEXTURE_MIN_FILTER`, `CANVAS_WEBGL_TEXTURE_WRAP_S`, `CANVAS_WEBGL_TEXTURE_WRAP_T`, `CANVAS_WEBGL_TRIANGLES`, `CANVAS_WEBGL_TRIANGLE_FAN`, `CANVAS_WEBGL_TRIANGLE_STRIP`, `CANVAS_WEBGL_UNPACK_ALIGNMENT`, `CANVAS_WEBGL_UNSIGNED_BYTE`, `CANVAS_WEBGL_UNSIGNED_SHORT`, `CANVAS_WEBGL_UNSIGNED_SHORT_4_4_4_4`, `CANVAS_WEBGL_UNSIGNED_SHORT_5_6_5`, `CANVAS_WEBGL_VENDOR`, `CANVAS_WEBGL_VERSION`, `CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_BUFFER_BINDING`, `CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_DIVISOR`, `CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_ENABLED`, `CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_NORMALIZED`, `CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_POINTER`, `CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_SIZE`, `CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_TYPE`, `CANVAS_WEBGL_VERTEX_SHADER`, `CANVAS_WEBGL_VIEWPORT`, `CANVAS_WEBGL_ZERO`, `CANVAS_WEBGPU_TEXTURE_DIMENSION_2D`, `CANVAS_WEBGPU_TEXTURE_FORMAT_DEPTH24_PLUS_STENCIL8`, `CANVAS_WEBGPU_TEXTURE_USAGE_RENDER_ATTACHMENT`, `CanvasContext2D`, `CanvasImageData`, `CanvasWebGLContext`, `WEBGPU_TEXTURE_DIMENSION_2D`, `WEBGPU_TEXTURE_DIMENSION_3D`, `canvas_arc`, `canvas_arc_with_direction`, `canvas_begin_path`, `canvas_clear_rect`, `canvas_close_path`, `canvas_create`, `canvas_draw_image`, `canvas_draw_image_region`, `canvas_ellipse`, `canvas_fill`, `canvas_fill_rect`, `canvas_fill_text`, `canvas_get_commands`, `canvas_get_context_kind`, `canvas_get_context_webgl`, `canvas_get_context_webgl2`, `canvas_get_image_data`, `canvas_line_to`, `canvas_measure_text`, `canvas_move_to`, `canvas_put_image_data`, `canvas_restore`, `canvas_rotate`, `canvas_save`, `canvas_scale`, `canvas_set_fill_style`, `canvas_set_font`, `canvas_set_line_width`, `canvas_set_stroke_style`, `canvas_stroke`, `canvas_stroke_rect`, `canvas_stroke_text`, `canvas_translate`, `canvas_webgl_active_texture`, `canvas_webgl_attach_shader`, `canvas_webgl_bind_buffer`, `canvas_webgl_bind_framebuffer`, `canvas_webgl_bind_renderbuffer`, `canvas_webgl_bind_sampler`, `canvas_webgl_bind_texture`, `canvas_webgl_bind_vertex_array`, `canvas_webgl_blend_color`, `canvas_webgl_blend_equation`, `canvas_webgl_blend_equation_separate`, `canvas_webgl_blend_func`, `canvas_webgl_blend_func_separate`, `canvas_webgl_buffer_data_size`, `canvas_webgl_check_framebuffer_status`, `canvas_webgl_clear`, `canvas_webgl_clear_color`, `canvas_webgl_clear_depth`, `canvas_webgl_clear_stencil`, `canvas_webgl_color_mask`, `canvas_webgl_compile_shader`, `canvas_webgl_compressed_tex_image_2d`, `canvas_webgl_compressed_tex_sub_image_2d`, `canvas_webgl_copy_tex_image_2d`, `canvas_webgl_copy_tex_sub_image_2d`, `canvas_webgl_create_buffer`, `canvas_webgl_create_framebuffer`, `canvas_webgl_create_program`, `canvas_webgl_create_renderbuffer`, `canvas_webgl_create_sampler`, `canvas_webgl_create_shader`, `canvas_webgl_create_texture`, `canvas_webgl_create_vertex_array`, `canvas_webgl_cull_face`, `canvas_webgl_delete_buffer`, `canvas_webgl_delete_framebuffer`, `canvas_webgl_delete_program`, `canvas_webgl_delete_renderbuffer`, `canvas_webgl_delete_sampler`, `canvas_webgl_delete_shader`, `canvas_webgl_delete_texture`, `canvas_webgl_delete_vertex_array`, `canvas_webgl_depth_func`, `canvas_webgl_depth_mask`, `canvas_webgl_depth_range`, `canvas_webgl_detach_shader`, `canvas_webgl_disable`, `canvas_webgl_disable_vertex_attrib_array`, `canvas_webgl_draw_arrays`, `canvas_webgl_draw_arrays_instanced`, `canvas_webgl_draw_buffers`, `canvas_webgl_draw_elements`, `canvas_webgl_draw_elements_instanced`, `canvas_webgl_drawing_buffer_height`, `canvas_webgl_drawing_buffer_width`, `canvas_webgl_enable`, `canvas_webgl_enable_vertex_attrib_array`, `canvas_webgl_finish`, `canvas_webgl_flush`, `canvas_webgl_framebuffer_renderbuffer`, `canvas_webgl_framebuffer_texture_2d`, `canvas_webgl_front_face`, `canvas_webgl_generate_mipmap`, `canvas_webgl_get_active_attrib`, `canvas_webgl_get_active_uniform`, `canvas_webgl_get_attached_shaders`, `canvas_webgl_get_buffer_parameter`, `canvas_webgl_get_context_attributes`, `canvas_webgl_get_error`, `canvas_webgl_get_extension`, `canvas_webgl_get_framebuffer_attachment_parameter`, `canvas_webgl_get_parameter`, `canvas_webgl_get_program_info_log`, `canvas_webgl_get_renderbuffer_parameter`, `canvas_webgl_get_sampler_parameter`, `canvas_webgl_get_shader_info_log`, `canvas_webgl_get_shader_precision_format`, `canvas_webgl_get_shader_source`, `canvas_webgl_get_supported_extensions`, `canvas_webgl_get_tex_parameter`, `canvas_webgl_get_uniform`, `canvas_webgl_get_uniform_location`, `canvas_webgl_get_vertex_attrib`, `canvas_webgl_get_vertex_attrib_offset`, `canvas_webgl_hint`, `canvas_webgl_is_buffer`, `canvas_webgl_is_context_lost`, `canvas_webgl_is_enabled`, `canvas_webgl_is_framebuffer`, `canvas_webgl_is_program`, `canvas_webgl_is_renderbuffer`, `canvas_webgl_is_sampler`, `canvas_webgl_is_shader`, `canvas_webgl_is_texture`, `canvas_webgl_is_vertex_array`, `canvas_webgl_last_buffer`, `canvas_webgl_last_framebuffer`, `canvas_webgl_last_program`, `canvas_webgl_last_renderbuffer`, `canvas_webgl_last_sampler`, `canvas_webgl_last_shader`, `canvas_webgl_last_texture`, `canvas_webgl_last_vertex_array`, `canvas_webgl_line_width`, `canvas_webgl_link_program`, `canvas_webgl_lose_context`, `canvas_webgl_pixel_store_i`, `canvas_webgl_polygon_offset`, `canvas_webgl_read_buffer`, `canvas_webgl_read_pixels`, `canvas_webgl_renderbuffer_storage`, `canvas_webgl_restore_context`, `canvas_webgl_sample_coverage`, `canvas_webgl_sampler_parameter_i`, `canvas_webgl_scissor`, `canvas_webgl_shader_source`, `canvas_webgl_stencil_func`, `canvas_webgl_stencil_func_separate`, `canvas_webgl_stencil_mask`, `canvas_webgl_stencil_mask_separate`, `canvas_webgl_stencil_op`, `canvas_webgl_stencil_op_separate`, `canvas_webgl_tex_image_2d`, `canvas_webgl_tex_parameter_i`, `canvas_webgl_tex_sub_image_2d`, `canvas_webgl_uniform_1f`, `canvas_webgl_uniform_1fv`, `canvas_webgl_uniform_1i`, `canvas_webgl_uniform_1iv`, `canvas_webgl_uniform_2f`, `canvas_webgl_uniform_2fv`, `canvas_webgl_uniform_2i`, `canvas_webgl_uniform_2iv`, `canvas_webgl_uniform_3f`, `canvas_webgl_uniform_3fv`, `canvas_webgl_uniform_3i`, `canvas_webgl_uniform_3iv`, `canvas_webgl_uniform_4f`, `canvas_webgl_uniform_4fv`, `canvas_webgl_uniform_4i`, `canvas_webgl_uniform_4iv`, `canvas_webgl_uniform_matrix2fv`, `canvas_webgl_uniform_matrix3fv`, `canvas_webgl_uniform_matrix4fv`, `canvas_webgl_use_program`, `canvas_webgl_validate_program`, `canvas_webgl_vertex_attrib_1f`, `canvas_webgl_vertex_attrib_1fv`, `canvas_webgl_vertex_attrib_2f`, `canvas_webgl_vertex_attrib_2fv`, `canvas_webgl_vertex_attrib_3f`, `canvas_webgl_vertex_attrib_3fv`, `canvas_webgl_vertex_attrib_4f`, `canvas_webgl_vertex_attrib_4fv`, `canvas_webgl_vertex_attrib_divisor`, `canvas_webgl_vertex_attrib_pointer`, `canvas_webgl_viewport`

**`test/unit/lib/debug/remote/t32_ffi/t32_types_spec.spl`** (17) <- `std.debug.remote.t32_ffi.t32_types`

> `T32_DEV_ICD`, `T32_ERR_APILOCK_FAIL`, `T32_ERR_ATTACH_FAIL`, `T32_ERR_COM_RECEIVE_FAIL`, `T32_ERR_COM_RECEIVE_TIMEOUT`, `T32_ERR_COM_TRANSMIT_FAIL`, `T32_ERR_EXECUTECOMMAND_FAIL`, `T32_ERR_FAIL`, `T32_ERR_NOMEMORY`, `T32_GROUP_CORE`, `T32_GROUP_EXECUTE`, `T32_REG_OBJ_R32`, `T32_REG_OBJ_R64`, `T32_STATE_DOWN`, `T32_STATE_HALTED`, `T32_STATE_RUNNING`, `t32_error_message`

**`test/unit/hardware/riscv_common/riscv_formal_contract_spec.spl`** (12) <- `hardware.riscv_common.core.riscv_formal`

> `RISCV_ECALL_INSTR`, `RISCV_PRIV_MACHINE`, `RISCV_PRIV_SUPERVISOR`, `RISCV_PRIV_USER`, `RV64_DEBUG_WRITE_ECALL_PC`, `RV64_DEBUG_WRITE_RESUME_PC`, `RiscvFormalContract`, `RiscvRetireEvent`, `riscv_instruction_size`, `riscv_mask_for_xlen`, `verify_riscv_event`, `verify_riscv_events`

**`test/unit/lib/common/compress_shared_helpers_spec.spl`** (12) <- `std.common.compress.utilities`

> `append_literal_copy`, `append_self_overlap_copy_avx2`, `append_self_overlap_copy_for_tier`, `append_self_overlap_copy_neon`, `append_self_overlap_copy_scalar`, `crc32_bytes_avx2`, `crc32_bytes_neon`, `crc32_bytes_scalar`, `decode_match_extension_length`, `xxhash32_bytes_avx2`, `xxhash32_bytes_neon`, `xxhash32_bytes_scalar`

**`test/unit/lib/gc_async_mut/gpu/browser_engine/css_ext_routing_spec.spl`** (10) <- `std.gc_async_mut.gpu.browser_engine.css`

> `css_get_flex_direction`, `css_get_flex_wrap`, `css_get_list_style_type`, `css_get_outline_color`, `css_get_outline_offset`, `css_get_outline_style`, `css_get_outline_width`, `css_get_width`, `css_value_as_i32`, `css_value_unit`

**`test/system/feature/web_platform/webgpu/webgpu_resources_spec.spl`** (10) <- `std.gc_async_mut.gpu.browser_engine.webgpu_resources`

> `WEBGPU_BINDING_TYPE_COMPARISON_SAMPLER`, `WEBGPU_BINDING_TYPE_NON_FILTERING_SAMPLER`, `WEBGPU_BINDING_TYPE_READONLY_STORAGE_BUFFER`, `WEBGPU_BINDING_TYPE_STORAGE_TEXTURE`, `WEBGPU_TEXTURE_DIMENSION_2D`, `WEBGPU_TEXTURE_DIMENSION_3D`, `WEBGPU_TEXTURE_VIEW_DIMENSION_CUBE`, `webgpu_find_texture_view`, `webgpu_validate_extended_texture_descriptor`, `webgpu_validate_texture_view_descriptor`

**`test/feature/web_platform/webgpu/webgpu_resources_spec.spl`** (10) <- `std.gc_async_mut.gpu.browser_engine.webgpu_resources`

> `WEBGPU_BINDING_TYPE_COMPARISON_SAMPLER`, `WEBGPU_BINDING_TYPE_NON_FILTERING_SAMPLER`, `WEBGPU_BINDING_TYPE_READONLY_STORAGE_BUFFER`, `WEBGPU_BINDING_TYPE_STORAGE_TEXTURE`, `WEBGPU_TEXTURE_DIMENSION_2D`, `WEBGPU_TEXTURE_DIMENSION_3D`, `WEBGPU_TEXTURE_VIEW_DIMENSION_CUBE`, `webgpu_find_texture_view`, `webgpu_validate_extended_texture_descriptor`, `webgpu_validate_texture_view_descriptor`

**`test/unit/browser/script/worker_api_spec.spl`** (10) <- `std.gc_async_mut.gpu.browser_engine.script.worker_api`

> `worker_create_with_secure_context`, `worker_global_gpu_available`, `worker_global_is_secure_context`, `worker_global_navigator`, `worker_global_post_message`, `worker_global_receive_message`, `worker_global_scope_create`, `worker_gpu_available`, `worker_is_secure_context`, `worker_navigator`

**`test/system/feature/web_platform/webgpu/webgpu_context_spec.spl`** (8) <- `std.gc_async_mut.gpu.browser_engine.webgpu_context`, `std.gc_async_mut.gpu.browser_engine.webgpu_resources`

> `WEBGPU_BINDING_TYPE_STORAGE_BUFFER`, `WEBGPU_BINDING_TYPE_STORAGE_TEXTURE`, `WEBGPU_TEXTURE_DIMENSION_3D`, `webgpu_adapter_status`, `webgpu_compatibility_mode`, `webgpu_diagnose_wgsl`, `webgpu_reflect_wgsl_bindings`, `webgpu_shader_module_diagnostic`

**`test/feature/web_platform/webgpu/webgpu_context_spec.spl`** (8) <- `std.gc_async_mut.gpu.browser_engine.webgpu_context`, `std.gc_async_mut.gpu.browser_engine.webgpu_resources`

> `WEBGPU_BINDING_TYPE_STORAGE_BUFFER`, `WEBGPU_BINDING_TYPE_STORAGE_TEXTURE`, `WEBGPU_TEXTURE_DIMENSION_3D`, `webgpu_adapter_status`, `webgpu_compatibility_mode`, `webgpu_diagnose_wgsl`, `webgpu_reflect_wgsl_bindings`, `webgpu_shader_module_diagnostic`

**`test/unit/lib/common/compress_framework_spec.spl`** (8) <- `std.common.compress`

> `decoder_finish`, `decoder_write`, `encoder_finish`, `encoder_finish_checked`, `encoder_write`, `new_decoder_state`, `new_encoder_state`, `try_compress_bytes`

**`test/unit/lib/common/compress_utilities_spec.spl`** (8) <- `std.common.compress.utilities`

> `append_bytes_range`, `compression_simd_runtime_profile_name`, `compression_simd_tier_from_simd_profile`, `compression_simd_tier_name`, `crc32_bytes_for_tier`, `push_many_byte`, `write_u16_be`, `xxhash32_bytes_for_tier`

**`test/unit/browser/script/navigator_api_spec.spl`** (7) <- `std.gc_async_mut.gpu.browser_engine.script.navigator_api`

> `navigator_gpu_adapter_available`, `navigator_gpu_adapter_request_device`, `navigator_gpu_bridge`, `navigator_gpu_preferred_canvas_format`, `navigator_gpu_request_adapter`, `navigator_gpu_request_adapter_status`, `navigator_gpu_secure_context`

**`test/unit/lib/common/proton_runtime_subsystems_spec.spl`** (6) <- `common.proton_runtime_subsystems`

> `proton_graphics_translation_gate`, `proton_non_wine_runtime_evidence_new`, `proton_pressure_vessel_gate`, `proton_steam_integration_gate`, `proton_steam_runtime_gate`, `proton_sync_gate`

**`test/unit/lib/common/wine_vm_adapter_spec.spl`** (6) <- `common.wine_vm_adapter`

> `wine_vm_adapter_feature_string`, `wine_vm_adapter_gate`, `wine_vm_mark_guard`, `wine_vm_region_contains`, `wine_vm_regions_overlap`, `wine_vm_space_new`

**`test/unit/lib/common/wine_process_session_spec.spl`** (6) <- `common.wine_process_session`

> `wine_process_bind_known_kernel32_imports`, `wine_process_cpu_dispatch_preflight`, `wine_process_inspect_full_imports`, `wine_process_plan_import_thunk_patches`, `wine_process_session_request_gate`, `wine_process_validate_full_image`

**`test/system/os/qemu/os/harden/cap_exec_gate_spec.spl`** (6) <- `os.qemu_systest_contract`

> `harden_cap_exec_markers`, `harden_image_path`, `harden_kernel_path`, `harden_qemu_args`, `harden_qemu_bin`, `harden_timeout_ms`

**`test/system/os/qemu/os/harden/hardened_malloc_spec.spl`** (6) <- `os.qemu_systest_contract`

> `harden_image_path`, `harden_kernel_path`, `harden_malloc_markers`, `harden_qemu_args`, `harden_qemu_bin`, `harden_timeout_ms`

**`test/system/os/qemu/os/harden/pie_ssp_relro_preset_spec.spl`** (6) <- `os.qemu_systest_contract`

> `harden_image_path`, `harden_kernel_path`, `harden_pie_relro_markers`, `harden_qemu_args`, `harden_qemu_bin`, `harden_timeout_ms`

**`test/unit/lib/engine/build_pipeline_spec.spl`** (5) <- `std.nogc_sync_mut.engine.build.build_config`, `std.nogc_sync_mut.engine.build.build_pipeline`

> `AssetBundle`, `AssetBundleEntry`, `BuildPipeline`, `BuildStep`, `BuildTarget`

**`test/unit/app/ui/capability_policy_spec.spl`** (4) <- `std.common.ui.capability`, `std.common.ui.capability_policy`

> `capability_to_string`, `default_deny_policy`, `deny_capability`, `grant_capability`

**`test/unit/lib/common/wine_arbitrary_pe_spec.spl`** (4) <- `common.wine_hello_exe`

> `wine_arbitrary_pe_can_probe`, `wine_arbitrary_pe_probe`, `wine_hello_exe_can_execute`, `wine_hello_exe_probe`

**`test/unit/lib/crypto/crypto_reference_spec.spl`** (4) <- `std.crypto.legacy_hash`, `std.crypto.pbkdf2`

> `get_recommended_pbkdf2_iterations`, `md5_hex`, `pbkdf2_sha512`, `pbkdf2_with_algorithm`

**`test/unit/os/apps/terminal/terminal_spec.spl`** (4) <- `os.apps.terminal.terminal`

> `AnsiState`, `TerminalChar`, `TerminalLine`, `default_char`

**`test/unit/os/compositor/shared_mdi_framebuffer_scene_spec.spl`** (4) <- `os.compositor.shared_mdi_framebuffer_scene`

> `render_shared_mdi_framebuffer_scene_for_lifecycle_windows`, `render_shared_mdi_framebuffer_scene_for_taskbar_render_input`, `shared_mdi_lifecycle_seed_windows`, `shared_mdi_seed_windows`

**`test/system/feature/app/t32_tools/t32_mcp_tools_spec.spl`** (4) <- `app.mcp_t32.action_tools`

> `t32_is_status_field`, `t32_normalize_current_status`, `t32_toolbar_run_enabled`, `t32_toolbar_stop_enabled`

**`test/unit/lib/blink/css_selector_spec.spl`** (3) <- `std.blink.dom.node`

> `attribute_new`, `dom_node_new`, `dom_tree_new`

**`test/unit/lib/common/wine_hello_fixture_spec.spl`** (3) <- `common.wine_hello_exe`, `common.wine_hello_fixture`

> `wine_hello_exe_can_execute`, `wine_hello_exe_probe`, `wine_hello_fixture_verified_gates`

**`test/unit/lib/common/wine_process_session_import_descriptor_table_spec.spl`** (3) <- `common.wine_process_session`

> `wine_process_inspect_import_descriptor_table`, `wine_process_inventory_import_descriptor_thunks`, `wine_process_plan_import_dependencies`

**`test/system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl`** (3) <- `common.wine_process_session`

> `wine_process_inspect_import_descriptor_table`, `wine_process_inventory_import_descriptor_thunks`, `wine_process_plan_import_dependencies`

**`test/unit/lib/engine/units_spec.spl`** (3) <- `std.common.engine.units`

> `FrameIndex`, `GamepadButtonId`, `PixelSize`

**`test/unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.spl`** (3) <- `lib.hardware.fpga_k26.k26_soc_top`

> `K26VexRiscvSocConfig`, `generate_k26_soc_top_vexriscv`, `k26_vexriscv_soc_config`

**`test/unit/lib/hardware/fpga_linux/synthesis_wrapper_vexriscv_spec.spl`** (3) <- `lib.hardware.fpga_linux.synthesis_wrapper`

> `add_verilog_sources`, `enable_axi_hp_port`, `synthesis_project_default`

**`test/unit/lib/http_server/rate_limit_spec.spl`** (3) <- `std.http_server.rate_limit`

> `check_rate_limit`, `default_rate_limit_config`, `new_rate_limit_store`

**`test/unit/lib/http_server/request_validation_spec.spl`** (3) <- `std.http_server.request_validation`

> `default_max_uri_length`, `validate_request_path`, `validate_uri_length`

**`test/unit/lib/http_server/csrf_spec.spl`** (3) <- `std.http_server.csrf`

> `default_csrf_config`, `is_csrf_exempt_method`, `validate_csrf_token`

**`test/unit/app/ui.chromium/css_spec.spl`** (2) <- `std.gc_async_mut.gpu.browser_engine.css`

> `css_get_flex_direction`, `css_get_gap`

**`test/unit/browser/script/console_api_spec.spl`** (2) <- `std.gc_async_mut.gpu.browser_engine.script.console_api`, `std.gc_async_mut.gpu.browser_engine.webgpu_context`

> `console_webgpu_shader_diagnostic`, `webgpu_diagnose_wgsl`

**`test/unit/browser_engine/html_tree_builder_spec.spl`** (2) <- `std.gc_async_mut.gpu.browser_engine.dom_accessors`

> `be_dom_get_attribute`, `be_dom_get_tag_name`

**`test/unit/compiler/mir_opt/collection_opt_spec.spl`** (2) <- `compiler.mir.mir_types`, `compiler.mir_opt.mir_opt.collection_opt`

> `collection_opt_optimize_function`, `mir_type_is_text`

## 9. Triage (2026-08-10)

This report is a census, not a single reproducible defect: it enumerates **782 distinct
missing modules** and **1003 distinct missing names** across **294 spec files**, spanning
whole unimplemented subsystems (blink layout, riscv64gc formal contract, canvas WebGL/WebGPU
constants, wine/proton process-session surfaces, compress SIMD tiers, LLVM backend for six
targets, http_server rate-limit/csrf/validation, etc). Closing it means writing hundreds of
missing modules and APIs — that is a large, multi-owner implementation backlog, not a
targeted root-cause fix a single triage pass can land.

The one genuinely *fixable, scoped* defect this report surfaces is the mechanism in §5.2:
a `use module.{A, B, C}` resolves and registers the whole target **module's** surface: the
braced name list is never checked member-by-member against it, so `B` can be nonexistent and
the spec still loads/passes silently (warning-only, buried in ~1,700 lines of lint noise) —
while an unresolvable **module** path is a hard error. That inconsistency (name-level:
warning + still-runs; module-level: hard error) is already tracked by its own reference note
(`reference_importing_one_symbol_registers_a_whole_module`) and is the correct place to land
a targeted fix (e.g. promote an unresolved braced-import name to an error, or at minimum
surface it above the lint-noise fold) — that is a compiler-frontend change to import-name
resolution, out of scope to bundle into this pass without risking a change that is itself
untouchable per this session's file-ownership constraints
(`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`,
`src/compiler/50.mir/_MirLowering/module_lowering.spl` are owned by another concurrent
session, and import-name resolution surface area was not independently re-scoped here).

**Disposition:** left OPEN as ARCHITECTURAL/OUT-OF-SCOPE for a single-pass fix. Re-verified
2026-08-10 that the underlying phenomenon (§5.2 sabotage proof) is unchanged — braced-import
names are still not checked against the resolved module's real surface — by inspection of
the current `module_loader_resolve.spl` name-registration path; a full re-run of the
`chacha20_spec.spl` mutation-arm proof was not repeated in this pass. Recommended next step:
file a scoped follow-up bug specifically for "braced `use` names not validated against module
surface" (name-checking behavior only, not the 782-module content backlog), and let the
1003-name/782-module backlog itself get triaged spec-family by spec-family (canvas/webgpu,
blink, riscv, wine/proton, llvm-backend, http_server) rather than as one bug.

## 8. Reproduce

```
git worktree add --detach <path> 53492af8dc4bb95e8bb11c18ec813f63e065b479
python3 census2.py <path> out.json     # census (walk MUST follow symlinks)
python3 validate.py <path> out.json val.json   # independent zero-occurrence confirmation
python3 classify.py <path> out.json rows.json  # module-resolves / does-not-resolve split
```


## STILL_PRESENT — re-verified 2026-08-17 (P2 triage, compiler lane)

Re-measured at HEAD 2026-08-17 with an independent census (symlinks followed,
realpath dedupe, decl keywords + bare `NAME =` + `export` lists + receiver forms;
braced `use` only, whole `test/` tree, duplicate test trees NOT collapsed):
**4290 distinct names missing across 1728 spec files**, out of 29405 distinct
imported names over 12390 spec files. Not directly comparable to the doc figure
of 1003/294 (different collapsing), but the same order or worse — nothing has
closed it. Still warning-only, never an error:
`src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:520` emits
`"[use-warning] {name} is named in \`use ...\` but module {} does not provide it"`
(deduped at `:516`, with no error path). NOT FIXED by this lane — this is a
policy decision (warn vs fail) with a 4290-name blast radius, not a local defect.
