# UTF-8 and Internationalized Text Development Guide

The authoritative research is `doc/01_research/lib/text_i18n/simple_utf8_internationalized_text_architecture_2026-08-25.md`. Requirements, architecture, detailed design, system/performance plans, and agent ownership use the matching `utf8_internationalized_text_architecture.md` files under `doc/02_requirements` through `doc/05_design`.

Development rules:

- preserve valid UTF-8 `text`; use byte types for undecoded input;
- state byte/scalar/grapheme/UTF-16/display units explicitly;
- keep scalar reference behavior executable and compare every optimization/backend to it;
- keep GUI/Web/WM semantic text in `DrawIrComposition` and transient font material in `FontRenderer`/`FontRenderBatch`;
- treat Engine3D as a sibling consumer, not a shortcut around Draw IR/Engine2D;
- use the existing canonical flat-AST zero-count inventory for Simple owners, but do not claim aggregate 100% until every text/i18n/rendering owner and native backend has a retained source-bound receipt;
- do not claim Engine3D world text or performance complete while the tracked projected-HUD/scene-composition blocker remains open;
- retain unavailable native rows as blocked with exact host/tool/artifact prerequisites.

The system-test plan lists focused commands and required evidence. Run each unchanged green acceptance command once per session and stop after three distinct fix/verify cycles.
