# HIR P2 HA2: stage3 native repro triage (2026-11-05)

Producer: copy of `C:/dev/p3new/s3new/s3_fable44.exe`, recipe
`C:/dev/p3new/s3sanity/run_case.ps1` (native-build --entry-closure, llvm,
x86_64-pc-windows-gnu, src/lib from the s3sanity shadow root), linked and run.
Repro programs: `test/fixtures/compiler/ha2_stage3/*.spl` (copy into
`<s3sanity root>/test/s3sanity/` and run `run_case_dir.ps1 -Name <stem>`).

| row | probe | result | outcome |
|---|---|---|---|
| a174_enum_tuple_literal_provenance_2026_10_16 | ha2_tuplit | PASS (`TupleOnly((7, 9))` untyped literal round-trips through match) | constructor-site provenance no longer reproduces in a standalone program; workaround in `test/04_smoke/enum_wire_boundary_native.spl` kept until that smoke is run natively without it |
| a174_aggregate_receiver_provenance_2026_10_16 | ha2_aggr, ha2_aggr2 | FAIL: `var r = Reg(keys: [...], rows: [...])` then `r.rows` iterates 0 times and `r.keys.contains("b")` is false — **with and without** the explicit `[text]` annotation | REPRODUCES, but the explicit-type workaround does not fix the probe; real defect is struct array-field read after struct-literal construction in native. Needs MIR/codegen lead; row stays open |
| a174_nominal_enum_operator_resolution_2026_10_16 | ha2_enumop | FAIL (runtime, rc=1): enum `==` via struct field inside `for` / `Option` return | REPRODUCES; diagnostic split ha2_enumop2 could not complete (see blocker) |
| a174_struct_nil_comparison_dispatch_2026_10_16 | ha2_nilcmp | not completed (blocker) | open |
| coherence_optional_payload_owner_2026_10_19 | ha2_optenum | not completed (blocker) | open |
| enum_payload_type_mismatch_tuple_pattern_binders_2026-10-24 | ha2_tupsubj, ha2_binders | not completed (blocker) | open |
| enum_named_payload_default_dropped_2026_10_16 | ha2_namedef | not completed (blocker) | open |
| a174_named_enum_payload_owner_2026_10_16 | — | not probed (marker sits on `HirType.named`; needs a stage3 self-build with it reverted) | open |
| a174_enum_scalar_codec_wire_boundary_2026_10_16 | — | not probed (generated-codec boundary; needs codegen regeneration + stage3 build) | open |
| caret_closure_enum_payload_binding_collection_gaps_2026_11_03 | — | not run (323-module Caret closure) | open |

Blocker: host C: free disk fell from 11.3 GB to 5.9 GB during the run; the
measure guard killed every later build (`CAP/LIMIT EXCEEDED`), and the shared
s3sanity snapshot also hit `workarounds: refresh failed:
src/lib/common/serialization/__init__.spl:407: workaround must immediately
precede the affected block` (someone else's edit in the shared root). Rerun the
remaining probes once disk is restored.
