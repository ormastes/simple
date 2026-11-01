# dir_tldr_aspect: Feature Requirement Options

**Status: AWAITING USER SELECTION.** Pick one option per group (some groups allow combining,
as noted). Unchosen options are deleted after selection. Effort: S ≤1 day, M 2-4 days, L 1-2 weeks, XL >2 weeks.

## A. Dir TLDR content and identity

| ID | Option | Pros | Cons | Effort |
|---|---|---|---|---|
| A1 | **Extend `PackageInitTldV1`** (`__init__.tld`): add `file_tldr_root_digest` (Merkle root of member file TLDR digests) and `join_point_facts_digest` (`directory_facts_key_v1`). Identity = (scope path, parent_scope_digest, membership_root, compiler/provider id, guard root). | Reuses the existing owner and the 10-30 plan; no parallel manifest | Wire bump for PackageInitTld; must remain parseable by stage2 | M |
| A2 | Separate `dir_tldr_v1` SDN attachment next to `__init__.tld`, referenced by digest | Leaves the PackageInitTld wire untouched; easier to evolve | A second manifest to keep consistent with the first | M |
| A3 | No stored dir TLDR: compute the dir view on demand from file TLDRs (current behaviour plus a cache) | Smallest change | Does not meet "check dir TLDR first"; no fail-closed artifact | S |

## B. Composition with file TLDR and generic/macro RR

| ID | Option | Pros | Cons | Effort |
|---|---|---|---|---|
| B1 | Dir TLDR stores only *roots* (digests) of file TLDRs, generic-TLDR views, and macro RR families. Detail stays in the existing owners. | Small; single source of truth | Needs an extra read to resolve detail | S-M |
| B2 | Dir TLDR inlines the public signatures of all member files (like rustc `.rmeta`) | One read serves sibling imports | Duplicates data; larger invalidation surface | L |
| B3 | B1 plus an inline join-point fact table (the only inlined data) | Weaving needs no per-file reads | Moderate size | M |

## C. Invalidation

| ID | Option | Pros | Cons | Effort |
|---|---|---|---|---|
| C1 | Early-cutoff recompute: rebuild the dir TLDR when any member TLDR digest, membership, guard root, or ancestor aspect root changes, and propagate to children only when its output digest changes | Precise; matches the RR coordinator model | Needs an old/new membership union (`OldNewMembershipV1`) | M |
| C2 | Rebuild on any member mtime/digest change, with no cutoff | Simple | Over-invalidates children and every aspect consumer | S |
| C3 | Route through the RR coordinator: dir TLDR facets become `ChangedSemanticFacetV1` subjects | Unified with generic/macro RR | Coordinator must learn a dir subject family | L |

## D. Scheduler policy

| ID | Option | Pros | Cons | Effort |
|---|---|---|---|---|
| D1 | **One job per dir with the dir TLDR resident, split when few.** If `dir_count < split_threshold`, split large dirs into chunks of ≥K files that share a read-only dir TLDR snapshot. Threshold = `min(jobs, mem_budget / per_job_rss_est)`, where jobs = 80. | Matches the user request; amortises the TLDR load | Large dirs serialise unless split; affinity logic in the scheduler | M-L |
| D2 | Per-file jobs (status quo) plus a dir-TLDR cache shared by memory map | Max parallelism; first `.o` is easy | Each job re-reads the dir TLDR (cheap if mapped) | S-M |
| D3 | Hybrid weighted bins: pack files into jobs by estimated cost, with dir affinity as a soft constraint | Best load balance | Most complex; needs cost estimates | L |

Threshold computation sub-options (combine with D1/D3):
- D-T1: static `dir_count < jobs`.
- D-T2: `dir_count < jobs` OR `max_dir_files > 4 × mean`.
- D-T3: cost-estimated (file bytes × history) with a target per-job wall of ≤10 s for the first object.

First `.o` ≤10 s rule (all D options): the first job's dir TLDR check must finish within a
2 s budget, and the scheduler orders the smallest ready dir first.

## E. Aspect object model

| ID | Option | Pros | Cons | Effort |
|---|---|---|---|---|
| E1 | **Traits `Aspect`, `Pointcut`, `Advice`, `Placement`**, with classes implementing them (as in `LogAspect`). The pointcut is a predicate object that compiles to the existing `PointcutSelectorV1` node array. | OOP and easy to change; reuses the selector wire | Needs a predicate→selector lowering | M |
| E2 | Text pointcut DSL only (the current selector text), with aspect classes that hold DSL strings | Minimal; DSL is already parsed and cached | Less type-safe; harder to refactor | S |
| E3 | Both: a DSL for authors plus an OOP predicate API, normalised to the same selector digest | Flexible | Two front doors to test | M-L |

## F. Pointcut→traversal plugin contract

| ID | Option | Pros | Cons | Effort |
|---|---|---|---|---|
| F1 | **`TraversalPlugin` trait:** `fn visit(dir: DirTldrView, sel: PointcutSelectorV1) -> WeavePlanDeltaV1`, which is pure and deterministic. Placement goes through a closed `Placement` enum (before / after_success / after_error / around / at_instruction) mapped to the existing inject_* functions. | Pure planning plus the existing weavers; testable | New placement kinds need an enum edit | M |
| F2 | The plugin also emits *new functions* (generated forwarders and helpers), placed into a synthetic per-dir module `__woven__.spl` | Supports "place functions" literally | New module identity; symbol collision rules | L |
| F3 | The plugin mutates HIR directly through a capability handle | Most powerful | Breaks purity and determinism; hard to cache | L |

## G. Plugin reuse identity

| ID | Option | Pros | Cons | Effort |
|---|---|---|---|---|
| G1 | **Plugin instance key** = digest(plugin code digest, normalised config with dir path and matcher removed). Dir path and matcher become call parameters. One instance is shared; per-dir *results* stay keyed by `pointcut_match_key_v1`. | Exact user intent; keeps the 10-30 rule that results are dir-scoped | Plugins must declare which config fields are "scope" | M |
| G2 | Reuse only the selector plan (status quo `aop_selector_plan_acquire_v1`) and instantiate a plugin per dir | No new identity | No instance reuse | S |
| G3 | G1 plus cross-dir result reuse when the dir facts digests are equal (identical subtrees) | More hits | Must prove that facts equality implies result equality | L |

## H. Hardening (multi-select)

| ID | Option | Pros | Cons | Effort |
|---|---|---|---|---|
| H1 | Fail closed when the dir TLDR is stale, missing, or invalid: refuse to admit the source compile, rebuild, and on failure fall back to the full visit (the existing conservative path), never using a stale result | Safety | Costs a rebuild | S |
| H2 | Determinism: sorted members, no timestamps, guard root in key; a spec compares the woven output of two runs byte for byte | Reproducible | Extra test time | S |
| H3 | Concurrency: dir TLDR production is single flight (`CacheSingleFlightV1`), readers pin an immutable generation, and publish is atomic via temp file + rename (the TLDR rule) | Avoids races | Requires the generation pin API | M |
| H4 | Corruption: framed digest check on every read (three-payload envelope); on mismatch, quarantine and rebuild | Robust | Small read cost | S |
| H5 | Plugin loading security: load only admitted plugins whose code digest is pinned in an SDN allowlist; no network; reject unsigned dynload | Supply-chain safety | Admin friction | M |
