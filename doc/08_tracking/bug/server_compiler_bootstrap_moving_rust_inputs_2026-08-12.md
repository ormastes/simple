# Server compiler bootstrap blocked by moving Rust inputs

Date: 2026-08-12  
Status: OPEN; source fixes retained, compiler publication not admitted

The strict native web and PostgreSQL-mimic server gates require an admitted
pure-Simple compiler. Three bounded bootstrap cycles were attempted against
`/mnt/data/bs2/final-current/bootstrap` with temporary storage on `/mnt/data`.

1. Cycle 1 failed in `simple-parser` with Rust borrow error E0502. The current
   source already contained the correct precomputed `requires [...]` guard;
   focused `cargo check -p simple-parser` then passed.
2. Cycle 2 built the Rust seed/native/runtime/backfill components, but correctly
   refused publication because Rust inputs changed during the build.
3. Cycle 3 again built through compiler backfill, then correctly refused stale
   publication. During that run, concurrent sessions changed runtime-symbol,
   call-codegen, interpreter-extern, and runtime-SFFI owners between 01:34 and
   01:35 UTC.

The publication refusal is a sound authority gate, not a compiler failure and
not server evidence. Per the three-cycle runaway cap, this session did not
retry. Logs, progress rows, and cache are retained under
`/mnt/data/bs2/final-current/`.

Recovery requires a fresh scoped session after `src/compiler_rust/**` is stable:
reuse the retained output/cache, run one full bootstrap, require Stage2/Stage3
sanity and deployment receipts, then run the strict web and DB native gates.
