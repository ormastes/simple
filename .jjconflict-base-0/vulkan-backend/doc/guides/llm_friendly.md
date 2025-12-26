# llm friendly features

Minimal context interface

System test public class/struct touch coverage

System test mock usage limits

Integration test public function touch coverage

Config-driven docs instructions

Task runner for coverage, docs, lint

Canonical formatter with “single correct style” (gofmt-style): eliminates stylistic variance so LLM output is predictable and diffs are meaningful.

AST/IR export as a first-class artifact (simplec --emit-ast/--emit-ir): enables deterministic machine checking, semantic diff, and downstream verification tools.

Stable, structured compiler diagnostics (error codes + JSON): makes “fix loops” reliable for LLM agents and reproducible for humans.

Explicit effect system / side-effect markers (@pure, @io, @net, @fs, @unsafe): prevents LLM from silently adding I/O or stateful behavior.

Capability-based imports (module requires declared capabilities): compile-time denial if code uses forbidden effects in a layer (e.g., domain logic cannot do net).

No implicit conversions policy + mandatory numeric widening rules: reduces subtle bugs and hallucinated coercions.

Exhaustiveness by default (match/enum/variant coverage required): blocks missing cases that LLMs often forget.

Non-null by default + explicit ?T: reduces “forgot to handle nil” mistakes and improves static guarantees.

Contract blocks (requires/ensures/invariant) with runtime + optional static checking: produces audit-friendly intent and catches LLM drift early.

Doctest / runnable spec snippets in docs: docs become executable; prevents docs/code divergence and lets humans verify quickly.

Golden/snapshot tests for public surfaces (API outputs, serialized forms): makes LLM regressions obvious and reviewable.

Property-based testing + fuzz harness generator for public functions and protocol parsers: catches edge cases LLMs typically miss.

Mutation testing gate (optional): measures whether tests actually detect wrong behavior (LLMs often write “weak tests”).

Spec coverage metric (requirements ↔ tests ↔ code traceability): distinct from line/branch coverage; verifies that each declared behavior is tested.

Public API “surface lock” file (generated manifest of exported types/functions/macros): prevents accidental API changes; reviewers diff one file.

Semantic diff tool (AST-level diff) in addition to text diff: avoids formatting-only noise and highlights real behavior changes.

Deterministic build mode (reproducible compilation + stable ordering): makes CI results consistent; reduces “works on my machine” from LLM output.

Minimal reproducible “replay logs” for failing tests (seed, inputs, environment hash): allows humans to re-run exactly what failed.

Context pack generator (per-target “needed symbols only” bundle): extracts minimal interfaces/types/docs used by a module so the LLM isn’t forced to ingest whole repos.

Strict module boundaries and layered architecture rules (lint-enforced): e.g., app/ may depend on domain/ but not vice versa; prevents spaghetti generation.

Forbidden pattern rules (configurable) with autofix: ban risky constructs, uncontrolled globals, unchecked indexing, ad-hoc parsing, etc.

“No hidden dependencies” policy (imports must be explicit; auto-imports recorded): LLMs often assume implicit availability—make it compile-fail instead.

Sandboxed execution runner for tests and tools (resource/time/network limits): ensures LLM-generated code can be safely verified.

Traceable provenance annotations (@generated_by, prompt hash, tool versions) in build artifacts (not necessarily in source): makes audits and blame assignment possible.

CI quality gates as first-class tasks: “must pass” gates for format, lint, typecheck, doc-build, unit/integration/system, coverage, spec-coverage, and (optionally) mutation score.


If you want, I can reformat your full list into a single “LLM Quality Contract” section (spec text) with: (1) required tasks, (2) failure categories, (3) artifacts to archive for human audit, and (4) default policies per test/unit|integration|system directory.
