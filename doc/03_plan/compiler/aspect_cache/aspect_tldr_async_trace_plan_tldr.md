# TLDR: aspect weaving through TLDR — plan (2026-11-28)

Full plan: `aspect_tldr_async_trace_plan.md`. Design: `doc/05_design/compiler/cache/aspect_tldr_async_trace.md`.

- 16 stages: AW-0, AW-0b, AW-1..AW-6, AW-7a, AW-7b, AW-8, AW-9, AW-9m, AW-10, AW-11, AW-12. Guide = Fable; Impl = sonnet except AW-9 (Fable); specs by sonnet or opus, written first.
- Start now (10): AW-0 gate lists + baseline, AW-0b existing modules to 95 %, AW-1 `aspect-decl|` section, AW-2 `JoinPointFactV2` + `join-point|` section, AW-3 selector identity, AW-4 explain, AW-5 plan + weave key + plan digest, AW-6 aspect plan receipt + real planner input + `aop-consumer` rows, AW-7a advice index as a pure fold, AW-11 trace fact rows.
- Wait for the engine (6): AW-7b async index (S1-3, S1-5), AW-8 persisted match under the sha256 identity (S2-6, S3-1, S3-5, A-2), AW-9 logical weave stage (S1-1, S1-2, S2-1, S3-4), AW-9m mir-family and log-rule weave stage (S1-2, S2-1), AW-10 zero reweave + hit replay + inline guard (B-1..B-3, S3-7), AW-12 pass deletion (S2-3, P-2).
- Trace surfaces (CLI, LSP, MCP) come from the one shared `TraceViewProjection` stage owned by the extreme-typing lane; generic S3-F8 and aspect AW-11 add fact rows.
- Gate (one script for both lanes): decision and condition coverage, 95 % per touched unit module, 70 % over the set, function-entered check, path normalisation; plus SSpec as document: every acceptance spec passes `sspec-maintain scan --min-score 80` and has its `doc/06_spec` mirror.
- Decided 2026-11-28: D1 advice-body edit rebuilds only the advice object + relink (inline-deps input is the guard; interim `inline|` rule; negative control in AW-10); D2 cached matching is forward + static before/after only, mir family is a coarse per-file key input; D3 shared projection stage; D4 decision/condition proxy.
