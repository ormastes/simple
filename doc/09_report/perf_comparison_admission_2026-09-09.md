# Cross-renderer performance comparison admission

Date: 2026-09-09

The C Vulkan/Simple and Chrome/Simple comparison lanes now share a fail-closed
admission contract in `scripts/check/lib/perf-comparison-admission.shs`.

## Required equal fields

`workload_id`, viewport width/height, warmup count, measured sample count,
timing scope, readback mode, capture mode, GPU identity, fallback state, source
revision, and checksum semantics were initially treated as equal fields. Review
corrected that rule: source revisions belong to different implementations, so
each source is now independently bound to its current SHA-256 and the hashes do
not need to match. The workload and every observation-boundary field still must
match, including the required output checksum.

Each exact-schema row binds a regular source file, executable binary, binary
admission receipt, and captured artifact to current SHA-256 values. Duplicate,
missing, empty, foreign-prefix, and unknown keys are rejected. Seed-like binary
paths, fallback/software GPU identities, mismatched devices, stale artifacts,
and symlinked evidence are rejected before a ratio is calculated.

The Chrome/Simple consumer additionally requires an exact JSON keyset, fixed
canonical fixture list, strict JSON types and positive finite p95, bundle-local
capture and receipt paths, and producer-specific binary kinds. JSON is parsed,
never sourced, and its projection is written to a private temporary directory.

## Evidence

The focused SPipe contract was expanded to cover independently pinned source
revisions, duplicate/unknown key injection, GPU mismatch, stale capture replay,
internally consistent seed-path rejection, and missing canonical Simple
artifacts. The existing C comparator fixture now emits the same artifact-bound
schema. Runtime SPipe execution remains pending an admitted pure-Simple CLI.
Direct artifact-only shell checks admitted independently pinned rows, admitted
a strict Chrome/Simple fixture at ratio 2000, and produced the expected C/Simple
1500 pass and 2500 fail. Mutation checks suppressed the ratio for duplicate JSON
keys, stale Chrome capture bytes, malformed p95, duplicate environment keys,
stale bound artifacts, and a hash-consistent `compiler_rust-seed` path. Shell
syntax and whitespace validation pass. No renderer or Vulkan benchmark was run,
and no performance claim is inferred from these contract checks.

An artifact-only check of the current Chrome/Simple directory returned:

```text
chrome_simple_web_status=skipped
chrome_simple_web_reason=missing-canonical-artifact
chrome_simple_web_ratio_x1000=0
```

This is an admission result, not a performance result. No C, Chrome, or Simple
renderer benchmark was run for this update, and no new timing number is
claimed.
