# Duplicate test-tree merge worklist (legacy vs numbered) — v3, SET-BASED

**Status:** OPEN — analysis only. No tree deleted, no merge performed here.
**Derived:** 2026-08-10 (v3) · supersedes v1 `44200dec485` and v2 `ed2f77a9c65`
**Component:** `test/01_unit` ↔ `test/unit`, `test/03_system` ↔ `test/system`
**Measured against:** committed tree at `origin/main` = `76fac4fbb9d` (never the shared working copy)
**Generator:** `scripts/check/check-duplicate-test-tree-merge-classes.shs` — output below is verbatim.

## Why a third derivation

| rev | metric | why it was wrong |
|-----|--------|------------------|
| v1 `44200dec485` | RAW line count | counts commented-out bodies; 44% of entries wrong |
| v2 `ed2f77a9c65` | CODE line **count** | a count cannot distinguish "legacy has 3 lines the twin lacks" from "legacy has 3 *more* lines, all already present in the twin". Audit `6546133e7b6` found its genuine-merge class empty — i.e. still misclassified. Its stripper also missed `//` line comments entirely. |
| **v3 (this)** | CODE line **set difference** | `uniq_a = code(a) \ code(b)`, `uniq_b = code(b) \ code(a)`. A pair is `genuine-merge` only when **both** are > 0. |

Comment stripping in v3 is a real scanner: `#`, `//`, `/* … */`, `"`/`'` strings
with backslash escapes, and `"""` triple-quoted strings — so a `#` inside a
string literal is code, not a comment.

## Classes

- `identical` — code-line sets equal. Delete either leg; no information loss.
- `adopt-superset-numbered` / `adopt-superset-legacy` — one leg is a strict
  code-line **subset**. Keep the superset, delete the subset. **Not a merge.**
- `genuine-merge` — both legs carry code lines the other lacks. Hand review.

## Verdict

**The `genuine-merge` class is NOT empty: 739 of 5,445 common pairs (13.6%).**
The two trees are therefore **not** pure duplicates and neither can simply be
deleted wholesale — 739 files would lose real assertions. The remaining 4,706
common pairs (86.4%) are collapsible mechanically (4,621 identical + 85
strict-subset).

Both trees execute (`test_runner_new` has no path allowlist; default root
`test/`, recursive), so every duplicated file is counted and run twice.

## Cross-checks (every headline number verified two independent ways)

| number | derivation A (this script) | derivation B (independent `git ls-tree`) |
|--------|---------------------------|------------------------------------------|
| `.spl` under the four roots | 18,206 | 7,631 + 5,105 + 3,532 + 1,938 = 18,206 ✓ |
| common pairs | 5,445 | 5,096 (unit) + 349 (system) = 5,445 ✓ |
| only-numbered | 5,718 | (7,631−5,096) + (3,532−349) = 5,718 ✓ |
| only-legacy | 1,598 | (5,105−5,096) + (1,938−349) = 1,598 ✓ |
| blob-differing pairs | 739 + 77 + 8 = 824 divergent, + 27 comment-only = 851 | `git ls-tree` blob-sha compare: 789 + 62 = **851** ✓ exact |

The last row is the strongest check: it never looks at line content at all, and
it lands on the same 851. The 27-pair gap between "blob differs" and "code
differs" is pairs differing only in comments/whitespace, which classify as
`identical` here by design.

## Genuine-merge magnitude

`uniq_leg` (unique code lines held only by the legacy leg) across the 739:

| uniq_leg | pairs |
|---|---|
| 1 | 196 |
| 2 | 69 |
| 3 | 228 |
| 4 | 62 |
| 5–9 | 71 |
| ≥10 | 113 |

So ~35% of the merge work is 1–2 lines (usually one `use` line plus one
assertion), but 113 pairs have ten or more legacy-only code lines.

## Script output (verbatim)

```
ref: 76fac4fbb9ddbe99d21f48432ce214c00403056e
spl files under duplicate roots: 18206
common (both-legs) pairs: 5445
only in numbered tree: 5718
only in legacy tree:   1598

== CLASS HISTOGRAM ==
   4621 identical
    739 genuine-merge
     77 adopt-superset-numbered
      8 adopt-superset-legacy

== PER-ROOT HISTOGRAM ==
   4333 test/01_unit <-> test/unit	identical
    682 test/01_unit <-> test/unit	genuine-merge
    288 test/03_system <-> test/system	identical
     73 test/01_unit <-> test/unit	adopt-superset-numbered
     57 test/03_system <-> test/system	genuine-merge
      8 test/01_unit <-> test/unit	adopt-superset-legacy
      4 test/03_system <-> test/system	adopt-superset-numbered

```

### Top 40 genuine-merge pairs by legacy-only code lines

```
374	269	470	365	test/01_unit/app/llm_caret/claude_cli_spec.spl
130	223	132	225	test/01_unit/app/llm_caret/openai_api_spec.spl
111	215	111	215	test/01_unit/app/llm_caret/claude_api_spec.spl
1	188	1	188	test/03_system/os_crypto_ref_helpers.spl
171	187	172	188	test/01_unit/app/llm_caret/config_spec.spl
192	144	217	169	test/01_unit/app/llm_caret/chat_spec.spl
9	134	69	194	test/01_unit/app/llm_caret/server_spec.spl
95	90	434	429	test/01_unit/app/tooling/command_dispatch_spec.spl
67	88	112	133	test/01_unit/compiler/types/platform_layout_attribute_spec.spl
61	79	119	137	test/01_unit/compiler/linker/platform_defaults_spec.spl
85	69	112	96	test/01_unit/lib/common/fault_detection_enhanced_spec.spl
70	68	339	337	test/01_unit/app/mcp_unit/tasks_spec.spl
65	65	239	239	test/01_unit/app/lsp/symbol_kind_spec.spl
14	63	326	375	test/01_unit/os/tls13/server_accept_spec.spl
27	63	136	172	test/01_unit/os/kernel/memory/vmm_vma_spec.spl
46	62	171	187	test/01_unit/lib/common/zstd_sequence_fse_execution_spec.spl
5	59	43	97	test/01_unit/os/installer/image_builder_artifact_spec.spl
59	59	147	147	test/01_unit/os/kernel/arch/syscall_dispatch_spec.spl
1	57	39	95	test/01_unit/compiler/backend/llvm_ir_builder_spec.spl
180	55	186	61	test/01_unit/browser_engine/html5lib_tokenizer_spec.spl
214	49	1443	1278	test/01_unit/compiler/backend/vhdl_backend_spec.spl
29	49	137	157	test/01_unit/lib/crypto/aes128_ccm_rfc3610_kat_spec.spl
40	45	76	81	test/01_unit/doctest/parser_spec.spl
110	44	191	125	test/01_unit/os/services/pm_service/pm_service_spec.spl
67	44	166	143	test/01_unit/compiler/loader/loader_shared_core_spec.spl
18	43	289	314	test/01_unit/app/tooling/test_runner_simple_spec.spl
43	43	145	145	test/01_unit/app/dap/debug_adapter_spec.spl
65	42	164	141	test/03_system/gui/arm64_wm_qemu_contract_spec.spl
12	41	202	231	test/03_system/database/server/db_server_tier_spec.spl
120	40	157	77	test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl
169	40	305	176	test/01_unit/os/compositor/wm_action_applier_spec.spl
254	40	475	261	test/01_unit/lib/skia/ot_parser_spec.spl
80	38	98	56	test/01_unit/lib/nogc_async_mut/http_server/protocol_handler_spec.spl
56	37	96	77	test/01_unit/os/kernel/smp/smp_spec.spl
9	37	92	120	test/01_unit/app/ui/backend_matrix_spec.spl
28	36	67	75	test/01_unit/lib/editor/extension_discovery_contract_spec.spl
63	36	79	52	test/03_system/os/e2e/simple_from_fs_spec.spl
187	34	187	34	test/01_unit/app/llm_caret/opencode_cli_spec.spl
30	34	204	208	test/03_system/gui/native_gui_build_spec.spl
34	34	144	144	test/01_unit/app/lsp/workspace_edit_spec.spl
20	32	249	261	test/01_unit/compiler/mir_opt/var_reassign_analysis_spec.spl
```

### Three concrete genuine-merge pairs, diverging code lines quoted

```
--- lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl
  ONLY IN test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl:
    | " data-wm-theme-bg='#123456'" +
    | " data-wm-theme-fallback='solid-material'" +
    | " data-wm-theme-material-mode='engine2d-cpu-composited-material-v1'" +
    | " style='display:block;width:12px;height:8px;" +
    | ""
    | """
    | "</body></html>"
    | "</div></body></html>"
    | "<body style='margin:0;padding:0'>" +
    | "<button id='invisible-button' style='opacity:0;width:16px;" +
    | "<div id='child' style='background:#22c55e;width:8px;height:8px'>" +
    | "<div id='inset' style='width:8px;height:8px;border-radius:10px;" +
  ONLY IN test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl:
    | expect(pixels[24 + 22 * 96]).to_equal(0xFFF59E0Bu32)
    | expect(simple.backend_name).to_equal("software")
    | it "default renderer uses the BrowserRenderer Engine2D software pixel path":
    | it "paints higher z-index absolute elements above lower z-index siblings":
    | simple_web_render_url_to_pixels}
    | val browser = BrowserRenderer.create_with_backend(120, 80, "software")
    | val html = "<html><head><style>.shell{position:relative;background-color:#e5e7eb;border:2px solid #0f172a;padding:4px;width:60px;height:42px}.base{background-color:#22c55e;width:36px;height:14px}.high{position:absolute;left:8px;top:6px;z-index:2;background-color:#f59e0b;width:30px;height:20px}.low{position:absolute;left:14px;top:10px;z-index:1;background-color:#1d4ed8;width:30px;height:20px}.next{background-color:#334155;width:24px;height:8px;margin-top:4px}</style></head><body><div class='shell'><div class='base'></div><div class='high'></div><div class='low'></div><div class='next'></div></div></body></html>"
--- lib/common/web/browser_session_spec.spl
  ONLY IN test/01_unit/lib/common/web/browser_session_spec.spl:
    | ""
    | "", "", "offline"
    | "'url(allowed.png)'"
    | "'url(failed.png)'"
    | "'url(https://cdn{denied_index}.test/blocked.png)'"
    | "'url(loaded.png)'"
    | "(event.currentTarget===probe)+':'+event.eventPhase;" +
    | ".card { width: 12px; height: 8px; background-color: #2563eb; }"
    | ".hero { background-image: url('../img/hero.png'); }", ""
    | ".hero{background:url('child.png') no-repeat}"
    | "/start.png"
    | "<button id='halt'>Halt</button><button id='probe'>Probe</button>" +
  ONLY IN test/unit/lib/common/web/browser_session_spec.spl:
    | "<html><head><link rel='stylesheet' href='/site.css'></head><body>styled</body></html>"
    | expect(false).to_equal(true)
    | expect(session.current_style_html).to_contain("background: rgb(1, 2, 3);")
    | session.register_resource("https://example.com/site.css", "body { background: rgb(1, 2, 3); }")
    | use std.gc_async_mut.web.browser_session.{BrowserSession, BrowserResponse}
--- os/compositor/wm_scene_spec.spl
  ONLY IN test/01_unit/os/compositor/wm_scene_spec.spl:
    | AppRef(app_id: "browser", display_name: "Browser", icon: "https://simple.local/icon.png")
    | SceneElement(kind: "control_center", x: -4, y: 40, w: 340, h: 120, color: 0xDD111827u32, text: "oversized"),
    | SceneElement(kind: "control_center", x: 460, y: 60, w: 260, h: 180, color: 0xDD111827u32, text: "controls"),
    | SceneElement(kind: "control_center", x: 520, y: 260, w: 340, h: 180, color: 0xDD111827u32, text: "wide controls"),
    | SceneElement(kind: "control_center", x: 520, y: 60, w: 280, h: 180, color: 0xDD111827u32, text: "controls"),
    | SceneElement(kind: "desktop_chrome", x: 0, y: 0, w: 240, h: 180, color: 0xFF101418u32, text: ""),
    | SceneElement(kind: "desktop_chrome", x: 0, y: 0, w: 800, h: 600, color: 0xFF101418u32, text: ""),
    | SceneElement(kind: "desktop_chrome", x: 0, y: 0, w: 900, h: 640, color: 0xFF101418u32, text: ""),
    | SceneElement(kind: "desktop_widgets", x: 20, y: 40, w: 280, h: 100, color: 0xCC111827u32, text: "oversized"),
    | SceneElement(kind: "desktop_widgets", x: 40, y: 230, w: 280, h: 140, color: 0xCC111827u32, text: "wide widgets"),
    | SceneElement(kind: "desktop_widgets", x: 40, y: 70, w: 220, h: 140, color: 0xCC111827u32, text: "widgets"),
    | SceneElement(kind: "snap_preview", x: 120, y: 42, w: 130, h: 100, color: 0x552563EBu32, text: "right")
  ONLY IN test/unit/os/compositor/wm_scene_spec.spl:
    | AppRef(app_id: "browser", display_name: "Browser", icon: "browser")
    | expect(all_in_bounds).to_equal(true)
    | expect(found).to_equal(true)
    | expect(has_clock).to_equal(true)
    | expect(has_command).to_equal(true)
    | expect(has_html).to_equal(true)
    | expect(has_name).to_equal(true)
    | expect(has_nonzero).to_equal(true)
    | expect(has_style).to_equal(true)
    | expect(has_width).to_equal(true)
    | expect(has_window_bar).to_equal(true)
    | expect(html.contains("Hidden")).to_equal(false)

```

## Reproduce

```sh
sh scripts/check/check-duplicate-test-tree-merge-classes.shs origin/main
```

The full 5,445-row pair table is printed by the script under
`== FULL PAIR TABLE ==` and is deliberately not inlined here.
