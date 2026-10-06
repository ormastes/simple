# Paired open-range owner integration

Candidate only; native qualification pending.

Base:5b1a6dbaee85ace4e1a0b47b97633dab62a2e806. Integrates exact source hunks and associated specifications, fixtures, manuals and bug evidence from cc7a0de35eb (parser absent endpoint ownership) and d75cfef5421 (MIR absent-end loop control). No static generic factory or parse-shard dispatch changes are included.

Parser uses missing node ID-1 instead of a real negative literal; authored negative endpoints remain present. MIR absent end branches directly to the body while bounded ends retain comparisons. Existing increment, continue, break and exit blocks are unchanged. The complete local for_collection_declared_type and subsequent collection-lowering/diagnostic source suffix is byte-identical to base after LF normalization; this is not an upstream whole-file replacement.

Upstream evidence is provenance, not a fresh Windows PASS: parser regression cases and MIR condition-shape assertions passed under diagnostic seeds. The earlier LLVM native probe still printed0 for the open case before the parser repair, and compiler teardown SIG139 remained a separate failure. Existing array range-index slicing and legacy interpreter/codegen endpoint gaps are not repaired here.

Required focused native qualification: a producer containing both repairs must compile and execute test/fixtures/bootstrap/open_range_break.spl and bounded_range_sum.spl. Each must print exactly6 followed by newline, stderr empty, compiler and executable exit0, canonical collector closure and no remnants. Compile exit failure is FAIL even if an artifact happens to execute correctly. Pin producer/source/runtime archive and use normal identity-validated private fixture caches. The seed interpreter cannot establish native MIR behavior.

No run launched: the shared160-job coordinator had all160jobs reserved at2026-10-06T07:18:42Z. Next focused run requires a real40-job reservation and complete immutable source composition; staging contains only this delta. Do not rerun unchanged upstream greens merely to generate a new receipt. Verify the composed-source owner cases once if composition changes require it; native execution remains the outstanding behavioral criterion.
