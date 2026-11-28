# TLDR: aspect weaving through TLDR — plan (2026-11-28)

Full plan: `aspect_tldr_async_trace_plan.md`. Design: `doc/05_design/compiler/cache/aspect_tldr_async_trace.md`.

- 14 stages, AW-0..AW-12 (AW-7 split a/b). Guide = Fable; Impl = sonnet except AW-9 (Fable); specs by sonnet or opus, written first.
- Start now, no engine dependency: AW-0 coverage gate + baseline, AW-1 `aspect-decl|` section, AW-2 `join-point|` section, AW-3 one selector identity, AW-4 explain, AW-5 plan + plan digest, AW-6 real planner input + `aop-consumer` rows, AW-7a advice index as a pure fold.
- Wait for the engine: AW-7b async index (S1-3, S1-5), AW-8 async persisted match (S2-6, S3-1, S3-5), AW-9 weave as a file-task stage (S1-1, S1-2, S2-1, S3-4), AW-10 zero reweave (B-1..B-3, S3-7), AW-12 pass deletion (S2-3, P-2).
- AW-11 trace: rows now; CLI, LSP and MCP once `TraceViewProjection` exists (decision D3).
- Gate: decision and condition coverage, 95 % per touched unit module, 70 % over the set, plus a function-entered check; one script shared with the generic lane.
- Owner decisions open: D1 advice-body edit rebuilds woven objects or not, D2 keep the forward / before-after restriction, D3 who builds `TraceViewProjection`.
