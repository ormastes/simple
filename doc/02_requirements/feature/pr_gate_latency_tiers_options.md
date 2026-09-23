<!-- codex-research -->
# PR gate policy options

## A. Minimal compile/validation required; other checks advisory

Description: keep one always-present required PR context. Code changes must hard-build and execute a current pure-Simple Stage 2 binary; docs-only validate repository/document structure; test-only validate changed test sources. Code Idiom and SPipe self-review remain visible advisory evidence, with release verification unchanged. Change the live main ruleset only after the new context is proven green on current heads.

Pros: matches the requested minimal merge gate; reduces required-check wait and permits risk-based verification. Cons: a compile smoke cannot catch semantic, platform, or SPipe-review defects; Stage 2 build may not meet a 10-minute wall-clock target, especially with runner backlog. Effort: L, roughly 5–9 workflow/config/test/doc files plus protected ruleset migration.

## B. Keep both current required contexts, optimize their work

Description: preserve Code Idiom and SPipe as mandatory; route audited path classes through fewer gate steps and fix live strict-policy drift.

Pros: retains current admission protection and exact-head review. Cons: runner queue remains the dominant delay; mandatory manual review and strict rebases may still exceed 10 minutes. Effort: M–L, roughly 4–8 files plus a live ruleset repair.

## C. Fast Rust-seed compile as the only required context

Description: require `cargo check` or a Rust seed build; keep pure-Simple build, Code Idiom, and SPipe advisory.

Pros: likely fastest check once scheduled. Cons: does **not** prove current pure-Simple sources compile or run and is weaker than the stated bootstrap policy. Effort: M, roughly 3–6 files plus protected ruleset migration.

User direction on 2026-09-23 selects a minimal compile-oriented gate and tiered docs/test/small-PR work, but the required proof target (Stage 2 versus Rust seed) is being clarified before policy migration.
