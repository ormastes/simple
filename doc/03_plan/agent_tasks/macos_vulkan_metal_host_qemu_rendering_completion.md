# macOS Vulkan/Metal and SimpleOS QEMU Rendering Completion

Updated: 2026-07-24

## Goal

Prove the same Simple 2D, web, GUI, vector-font, and event behavior through
Vulkan (MoltenVK) and Metal on macOS, then prove the applicable WM/2D behavior
on SimpleOS under QEMU. Evidence must include real backend initialization,
device readback, a positive backend handle, semantic pixel checks, visible
capture, and keyboard/pointer/click delivery. Vector-font evidence must cover
the canonical `FontRenderer` path and the requested 300 DPI configuration.

## Current State

| Lane | State | Current evidence or blocker |
|---|---|---|
| macOS Vulkan environment | PASS | MoltenVK initializes on Apple M4 through `/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json`. |
| Vulkan vector pipeline creation | PASS (focused) | The 2026-07-24 minimal provider probe reported session init `0`, backend ready, pipeline `ready`, artifact `precompiled-spirv`, device `Apple M4`. |
| Vulkan vector composite/readback | FIXED, NOT REVERIFIED | Descriptor bindings 0–2 were added. Font download now uses `vulkan_sffi_read_buffer_bytes`; the previous probe stopped at the now-removed `rt_vulkan_copy_from_buffer` interpreter gap. The three-attempt composite cap was reached before rerun. |
| Vulkan web render/events | FAIL | No live window/event capture. The last bounded source-interpreted launch exceeded about 1.5 GiB RSS before window discovery. Asset-root, rerender, checksum, and event checks were fixed. |
| Vulkan widget GUI/render/events | FAIL | A 320×240/96 DPI device frame and vector-cache evidence were produced, but the old provider reported `font-pipeline-not-ready` and exited before window/event capture. The provider now creates the pipeline, but the live gate has not been rerun. |
| 300 DPI vector GUI | NOT PROVEN | The 1200×900/300 DPI attempt exceeded about 1.5 GiB before a window appeared. Font probing was subsequently changed to `dlopen` before reading the font, reducing the 96 DPI path to about 332 MiB. |
| Metal 2D | OTHER-AGENT LANE | Preserve the local Engine2D comparison worktree. The recovered `index 63375` failure belongs to Metal 2D GPU-only CPU composition with an empty software mirror, not the Vulkan GUI lane. |
| Host WM | FAIL | The live gate exhausted three attempts at native build. Chained/temporary string calls in the self-hosted native-build closure are now hoisted, but focused native build next exposed stale deployed-runtime support for `rt_array_free`. |
| QEMU SimpleOS SIMD/2D | FAIL / UPSTREAM CODE PRESENT | Local commit `7f7adc806a` must not be cherry-picked: its seven code/script blobs already landed upstream as `dc890ae58e`; its report is stale. Existing evidence is static prerequisite evidence only and lacks guest framebuffer, hashes, bounds, events, and runtime SIMD receipts. |
| QEMU WM | NOT STARTED | Must follow a host-WM PASS. |
| Git sync | FETCHED, NOT PUSHABLE | The shared root mixes rendering work with unrelated LLM-caret and local-agent 2D changes. Current work is being transferred to an isolated worktree rooted at `origin/main`. |

## Fixes Present in the Shared Working Copy

- macOS GUI launcher forwards the repository asset root and bounded backend/event
  evidence settings.
- Web examples rerender after input and cross-check device-readback checksums.
- The Vulkan widget evidence wrapper now fails fast when the app exits and
  records bounded stdout/stderr causes instead of masking them as a window
  timeout.
- Font provider probes open the provider library before loading a large font,
  avoiding repeated boxed copies of a 17.7 MiB font.
- The macOS Vulkan provider exposes storage-buffer bindings 0, 1, and 2 for the
  shared vector-font compute shader.
- Vulkan font composite readback uses the canonical returned-byte API rather
  than an interpreter-incompatible mutable-array extern.
- Host WM uses stable executor accessors, receiver-local window rendering, and
  sequential JSON escaping.
- Self-hosted compiler/CLI hot paths no longer invoke `replace` on temporary or
  chained receivers that the deployed stage-4 interpreter cannot dispatch.

## Remaining Work in Order

1. Finish the isolated rendering worktree transfer and confirm no LLM-caret,
   local Metal/2D, stale FAIL report, or unrelated deletion is included.
2. Run a full bootstrap in that worktree because both `src/compiler_rust` and
   pure-Simple compiler sources changed:

   ```sh
   scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy
   ```

3. With the newly deployed pure-Simple binary, run each focused native fixture
   once:

   ```sh
   SIMPLE_LIB=src bin/simple native-build \
     --source test/fixtures/compiler/native_module_global_initializer.spl \
     --entry test/fixtures/compiler/native_module_global_initializer.spl \
     --entry-closure --strip --backend cranelift --mode dynload \
     --output build/focused-module-init

   SIMPLE_LIB=src bin/simple native-build \
     --source test/fixtures/compiler/native_class_array_param_field_mutation.spl \
     --entry test/fixtures/compiler/native_class_array_param_field_mutation.spl \
     --entry-closure --strip --backend cranelift --mode dynload \
     --output build/focused-method-symbol
   ```

4. In a fresh verification session, run the focused Vulkan font composite spec
   once and require promoted device execution, fence completion, nonzero
   readback bytes, and matching device/oracle checksums.
5. Rerun Vulkan web and widget GUI live gates in a fresh session. Require
   window capture plus focus, keyboard/input, pointer, and click receipts.
6. Repeat the widget GUI at 300 DPI after the bounded 96 DPI path passes.
7. Run the host WM production fullscreen gate and require native artifact,
   semantic capture, taskbar/window evidence, and routed input.
8. Only after Vulkan lanes pass, execute equivalent Metal web/GUI/WM checks and
   integrate the other agent’s Metal/2D result without absorbing its dirty
   worktree.
9. Run the QEMU SimpleOS 2D/SIMD evidence gate with real guest framebuffer and
   runtime receipts, then the QEMU WM gate after host WM passes.
10. Run rendering source-coupling, direct-runtime, numbered-artifact,
    spec-layout, compiler/core/lib/MCP/LSP, and scoped production verification
    gates. `STATUS: PASS` is required before commit or push.
11. Commit only the isolated verified lane, fetch/rebase linearly onto
    `main@origin`, apply the file-count guard, set `main`, and push.

## Parallel Ownership

| Lane | Owner | Merge rule |
|---|---|---|
| Host Vulkan web/GUI/font provider | Primary agent | Merge only after live device/capture/event PASS. |
| Host/QEMU 2D Vulkan/Metal/SIMD comparison | Existing local agent | Do not duplicate or absorb dirty files; accept only reviewed committed evidence. |
| Host WM/compiler bootstrap | Primary agent | Host PASS precedes QEMU WM. |
| Final verification | Highest-capability primary reviewer | Review all sidecar findings and issue the final PASS/FAIL result. |

Merge owner: primary agent. Final reviewer: primary highest-capability agent.

## Stop Conditions

- Do not repeat an already exhausted gate in the same session.
- Stop after three fix/verify cycles for one feature and record the exact
  remaining failure.
- Do not claim GPU proof from CPU mirrors, upload-only receipts, synthetic
  handles, static screenshots, or source checks.
- Do not commit or push FAIL reports as completion evidence.
- Do not mark the overall goal complete until every row required by the goal
  has authoritative PASS evidence.
