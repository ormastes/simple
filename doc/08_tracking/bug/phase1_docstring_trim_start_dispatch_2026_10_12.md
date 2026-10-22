# Phase1 doctest discovery trim_start dispatch gap

Status: OPEN underlying dispatch bug; tagged source compatibility candidate.

Actual pinned49e bootstrap whole-listing reached18,978 spec paths then failed at str.trim_start in the source docstring extractor. No fourth listing was run. Whole tests remain unqualified.

The extractor already computes trimmed = line.trim(). The candidate derives leading indentation from the first occurrence of that trimmed content, using the original line length when it is whitespace-only. Nonempty trimmed content starts with non-whitespace, so cannot occur in the leading whitespace. The original line remains the body source, preserving trailing spaces and indentation. No runtime/provider API, source exclusion or silent skip changes.

Actual bounded Phase1 bootstrap diagnostic: primitive7/7 PASS in2.014s, sampled tree peak159105024B. UTF8 EM SPACE plus NBSP has byte offset5, consistent with text length. Actual modified extract_doctests6/6 PASS in2.527s, sampled tree161439744B (child172600KiB), against real ASCII/tab/Unicode/blank/repeated payload/nested sdoctest files with exact body assertions including trailing spaces. Exact seed/runtime/source pins are in the adjacent evidence JSON. Existing runtime-family warnings were retained. Previous green checks were not repeated.

Packaged regression changes only fixture path literals to the dedicated repository directory. Assertions and fixture bytes are unchanged; portable path adaptation is source-reviewed and not claimed as rerun. Timing/RSS are focused diagnostic bounds, not a before/after optimization comparison. Underlying method dispatch, whole discovery, production selfhosted compiler/lib/MCP/LSP gates and native/other-platform execution remain OPEN or unexecuted. This is authorized bootstrap diagnostic source execution, not a production Rust fallback.
