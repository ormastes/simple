# SPipe Knowledge Compiler — Refined, Parallelizable Plan (pure Simple)

Refines `doc/01_research/infra/spipe/spipe_project_local_knowledge_pair_expert_pr_balancing.md`
(the selected final design) into a buildable, YAGNI-reduced sequence.
Audience: implementing agents. Verified against the tree on 2026-08-31.

**Revision 2 (2026-08-31): implementation language is pure Simple.** Revision 1
concluded "all Slice-1 packages target JS because the package is JS". That
conclusion is rejected. CLAUDE.md's rule — ALL code in `.spl`/`.shs` — is the
direction of travel, not a description of the tree; the 8.6k-line JS package in
`examples/05_stdlib/spipe` is **legacy to be superseded**, not a precedent that
licenses more JS. New implementation is `.spl` under `src/app/spipe/`.

---

## 1. GROUND TRUTH (unchanged from revision 1 — still accurate)

### 1.1 `examples/05_stdlib/spipe` — this IS the current SPipe package, and it is JavaScript

Not `.spl`. 344 files; `src/` is 8,649 lines of ES modules (`"type": "module"`,
package `@simple-lang/spipe` v0.2.0). `test/` is 4,106 lines of `node --test`.
The only Simple in it is two parity probes: `test/support/dbfs_wave4_parity_probe.spl`,
`test/support/simple_provider_wave4_parity_probe.spl`.

Module inventory (what exists and is tested): model records + UID derivation
(`src/model/*.js`, ~1,400 lines), `KnowledgeCompiler`/`compileKnowledgeGraph`
(`src/core/`, ~1,000), line-scan markdown/SDN/sspec parsers (`src/parser/`,
~760), trace extraction with `links_to` candidates from trace markers only
(`src/extract/trace.js:196`), `GraphStore` with signed cursors and work-unit
limits (`src/graph/store.js`, 403), content-addressed snapshot store with CAS
(`src/storage/`, ~1,000), BM25/exact/fusion retrieval + Unicode 17 tables
(`src/index/`, `src/search/`), portable provider protocol (`src/provider/`),
workspace registry (`src/workspace/`), CLI dispatcher with host + 58 fine-tune
commands (`src/cli/`, 1,982), 9-line MCP stub (`mcp/server.js`).

**Absent entirely** (verified by grep): generic markdown inline/reference **link
extraction**; any **reverse/incoming-edge index**; any **balance / score /
cohesion / rebalance / Leiden** code; any refactor/move transaction or journal;
any PR admission logic; a skill compiler.

**The knowledge core is unreachable from any surface.** `grep -rn
"knowledge_compiler\|knowledge_graph" cli/ src/cli/ mcp/` returns zero hits. The
CLI dispatches only host + fine-tune commands; the MCP server is a 9-line stub.
8.6k lines of core is library-only.

### 1.2 `.spipe/spipe` — an older generation, not a mount of the above

Own `.git`, **no `src/` at all**; `cli/spipe.js` is self-contained, version
0.1.0 vs the example's 0.2.0. This is the "independently versioned writable
duplicate" research §2.3 wants removed. Cross-repo; deferred (debt #2).

### 1.3 Existing SIMPLE assets (new in revision 2 — this changes the port math)

The repo already carries pure-Simple SPipe-adjacent code:

- `src/app/spipe_knowledge_provider/` — 38 `.spl` modules including
  `canonical_json_emitter.spl`, `canonical_json_decoder.spl`,
  `streaming_sha256.spl`, `lexical.spl`, `provider_utf8_decoder.spl`,
  `segmented_bytes.spl`, durable lifecycle + wire protocol. Canonical bytes and
  hashing exist in Simple already.
- `src/app/spipe_docgen/`, `src/app/spipe_process_harness/` — sibling SPipe apps.
- `src/lib/common/markdown/` — a small (586-line) block/inline markdown parser.
  **No byte offsets, no link records** — verified; unusable for rewriting, usable
  as a test oracle.
- stdlib crypto: `src/lib/common/crypto/sha256`.

### 1.4 Delta vs the research doc's 12 waves

Same as revision 1: W0 partial, W3 ~60% *in JS* (models/graph/snapshot/delta;
link extraction + reverse index missing), W5 ~40% in JS, everything else not
started. Retrieval (BM25/fusion/provider) is fully built in JS but maps to no
research wave. **Revision-2 reading:** the JS "~60%" is inventory of the legacy,
not a head start — the Simple port's Slice 1 needs only a thin subset of it
(records, UID derivation, edge model), and 1.3 shows the hashing substrate
already exists in Simple.

---

## 2. CORRECTIONS TO THE RESEARCH DOC (unchanged where noted)

### 2.1 SPK diagnostic-code collisions — real, four of them (UNCHANGED, still binding)

§12 assigns codes already used by shipped JS **and asserted in its tests**:

| Code | §12 assigns | Already means (file:line) |
|---|---|---|
| `SPK704` | balance plan stale vs head | cursor/pin invalid/expired — `src/graph/store.js:159,201,287,362,387-400`; `src/storage/graph_snapshot_store.js:303,324` |
| `SPK901` | required expert pair absent | snapshot CAS conflict / worktree owned — `graph_snapshot_store.js:203,343`; also arch + design docs |
| `SPK902` | pair handoff lacks acceptance | stale graph delta / `before_hash` mismatch — `store.js:83-114,333,345,370`; `graph_snapshot_store.js:269` |
| `SPK803`/`SPK804` | (8xx block §12 claims) | object hash/canonicalization failures, stage consumed — `graph_snapshot_store.js` (12 sites) |

The SPK namespace is shared across docs + both implementations, so the legacy JS
keeps its codes **reserved forever**, even after retirement — docs and old
snapshots cite them. Full census of taken codes (`doc/` + example):
001–023, 101–104, 201–205, 301–302, 401, 406, 501, 601–609, 701–707, 801–804,
901–902. New codes only from: link/graph **SPK110–129**, balance **SPK510–529**,
admission **SPK530–549**. Do **not** use §12's SPK704/901/902; do not renumber
anything shipped. Registry file moves to Simple ownership (see S1-D), format SDN.

### 2.2 Requirement IDs (UNCHANGED)

`doc/02_requirements/feature/spipe_knowledge_compiler.md` defines REQ-SPKC-001–030;
research §23.2 defines 032–038; **031 is a skipped number, not a collision** — do
not renumber. New requirements start at 039.

### 2.3 Wave-number ambiguity (UNCHANGED)

The example's `wave2/3/4` test/fixture names are the OLD knowledge-compiler
plan's waves, not the research doc's 0–12. "Wave N" here always means the
research doc's numbering; existing fixtures keep their names.

### 2.4 Corrections the LANGUAGE switch adds (new)

Things in the research design that pure Simple makes wrong or awkward — amend
the research doc separately:

1. **§22 target source structure is a JS tree** (`*.js` modules inside the npm
   package). The canonical implementation now lives in this repo at
   `src/app/spipe/` as `.spl`; §22's layout survives only as a namespace
   sketch. The npm package becomes a distribution/legacy shell, not the home.
2. **§2.3 step 7 ("Simple is an optional acceleration provider behind the JS
   protocol") is inverted.** Simple is the owner; if anything, JS becomes a
   compatibility surface. The provider protocol survives — but its reference
   implementation is `spipe_knowledge_provider` (already `.spl`), and the JS
   `js_fixed_point.js` becomes the parity foil, mirroring the existing
   `.spl` parity probes in reverse.
3. **§9.1 "use an AST, not regular expressions"** — still no CommonMark AST
   exists, in either language. `std.common.markdown` parses blocks/inline but
   carries **no source offsets**, which link rewriting requires. The deviation
   stands (offset-carrying region-exclusion scanner), but the reason changed:
   it is no longer "no new dependencies", it is "no offset-preserving parser
   exists"; the stdlib parser is available as a free cross-check oracle in
   tests. Extending `std.common.markdown` with offsets is the recorded
   long-term fix (debt #1).
4. **§13/§16 "identical score on Linux and Windows" via canonical JSON** — in
   Simple, canonical bytes come from `spipe_knowledge_provider`'s
   `canonical_json_emitter.spl` / SDN canonicalization, not JS `canonicalBytes`.
   Same requirement, different substrate; the research doc should stop naming
   JS functions as the mechanism.
5. **§20 CLI surface** assumed extending the JS `dispatcher.js` with legacy
   byte-identical-output constraints. The Simple CLI is a new `src/app/spipe`
   entrypoint; the legacy-output and `legacy_cli_perf_test.js` constraints
   apply only to the frozen JS package and no longer constrain new work.
6. **§25 ownership table** assumes 9 JS workstreams; superseded by §4 below.
7. **`admit` keyword**: the research doc's `knowledge admit` verb and
   `AdmissionVerdict` type are implementable, but `admit`/`assume` were hard
   keywords until 2026-08-21 and are contextual **only on a rebuilt seed**.
   Not a design change — a build-order dependency the research doc doesn't know.

### 2.5 Ownership claim (UNCHANGED)

§2.3 step 5 cannot be executed from this repo (`.spipe/spipe` is a separate git
repo). All new work targets this repo; the JS example is frozen in place.

---

## 3. LANGUAGE, LOCATION, MIGRATION

### 3.1 Location: `src/app/spipe/`

New directory. Fits `.claude/rules/structure.md`: `src/app/` is "Applications",
and three SPipe siblings already live there (`spipe_docgen`,
`spipe_knowledge_provider`, `spipe_process_harness`). Tests mirror at
`test/01_unit/app/spipe/*_spec.spl` (SSpec), fixtures under
`test/fixture/spipe/slice1_*/`. Config/registry data files are **SDN** (project
rule), not JSON. Keep modules small — lint cost is superlinear in file content
(see `.claude/rules/commands.md`); do not port the 8.6k-line shape 1:1, and no
single `.spl` should exceed a few hundred lines.

### 3.2 Migration stance: greenfield Simple; JS frozen, then retired

**Key fact from §1.1: Slice 1 was greenfield even under the JS plan.** All four
Slice-1 capabilities (link extraction, reverse index, balance score, admission)
exist in **neither** implementation, and the JS knowledge core is reachable from
no CLI/MCP surface. Switching languages therefore strands almost nothing:
nothing depends on JS code that Slice 1 would have extended.

What happens to the 8.6k working JS lines:

- **Frozen legacy, effective immediately.** `examples/05_stdlib/spipe` accepts
  bug fixes only; no new features land there. Its host + fine-tune CLI commands
  and its `node --test` suites keep working untouched — nothing in Slice 1
  edits any JS file, so nothing can break them.
- **Still-live dependents:** only its own tests/build (`scripts/build.shs` `cmp`
  equality) and the two `.spl` parity probes. No repo tooling imports it
  (verified in revision 1: core unreachable). `.spipe/spipe` 0.1.0 is
  independent legacy (debt #2).
- **Port order = need order, not module order.** Slice 1 ports only the record
  model + UID/edge subset it needs (S1-E below). The graph store, snapshot
  store, retrieval stack, and fine-tune CLI are ported in later slices *when a
  Simple feature needs them* — or retired unported if nothing ever does
  (retrieval may be subsumed by `spipe_knowledge_provider`).
- **Parity, not faith:** while both exist, the JS model/identity tests are the
  oracle — S1-E's spec asserts UID derivation matches fixture vectors generated
  once from the JS implementation and checked into `test/fixture/spipe/uid_vectors.sdn`.
- **Retirement (research W12)** happens when the Simple CLI covers the host
  commands actually used; tracked as debt, not scheduled here.

### 3.3 What the JS→Simple switch changes in the plan

Easier:
- **Tests are SSpec `*_spec.spl`** run by `bin/simple test` — same runner and
  reporting as the whole repo; mutation-red discipline applies (every spec must
  pass AND fail under an injected bug).
- **Real records**: frozen-object emulation (`deepFreeze`, `immutableRecord`)
  disappears; Simple value semantics give immutability by default. Enums replace
  string unions (`EDGE_TYPES` etc.).
- **`Result<T,E>` + `?`** replaces `fail()`/throw — the S1-B journal contract
  becomes typed instead of exception-shaped.
- **Reuse**: canonical JSON, streaming SHA-256, lexical compare already exist in
  `spipe_knowledge_provider`; stdlib sha256, SDN parsing, path/text utils are
  free. The "zero new dependencies" constraint dissolves — the repo's stdlib IS
  the dependency budget.
- **No legacy-CLI compatibility constraints**: no byte-identical output, no
  lazy-import perf dance, no `rebalance`/`promote` exposure spec to tiptoe
  around (that spec binds the *released JS CLI*, which we don't touch).

Harder / different:
- All Simple-specific hazards in §3.5.
- No `node --test` conveniences (subtests, process-kill fault injection is
  DIY): S1-B's fault injection uses a journal-replay harness (write journal,
  simulate truncation at each state, re-open) rather than killing processes.
- The seed-version dependency for `admit` as an identifier (§2.4.7).

### 3.4 Markdown parser question, re-decided on its merits

Decision: **write an offset-carrying link/region scanner in Simple**
(`src/app/spipe/scan/`), NOT adopt `std.common.markdown` as the extractor, NOT
write a CommonMark AST.

- The dependency constraint no longer binds — but the stdlib parser records no
  byte offsets and no link nodes (verified), and rewriting requires exact byte
  ranges. Retrofitting offsets into it is a stdlib API change with its own
  blast radius; out of scope for Slice 1, recorded as the preferred debt-payoff
  path (debt #1).
- A full CommonMark AST remains a multi-week task with no Slice-1 payoff: the
  scanner needs exactly (a) fenced-block + code-span region exclusion,
  (b) inline / reference-definition / reference-use / autolink forms,
  (c) heading offsets + slugs. That is a bounded, testable surface.
- New in Simple: S1-A's spec cross-checks against `std.common.markdown` as an
  oracle — every link the scanner finds must appear in the stdlib parse's
  inline output (existence, not offsets), catching scanner false positives for
  free.

### 3.5 Simple-specific hazards (binding on every package)

From `.claude/rules/code-style.md`, `.claude/rules/language.md`, and memory:

1. **`text.len()` is BYTES; `s[i]` indexes CHARS.** Every `while i < s.len()`
   + `s[i]` scanner traps or corrupts on non-ASCII — and doc prose IS
   non-ASCII (em-dashes, arrows, box drawing throughout `doc/`). The scanner
   MUST work on one representation consistently. **Rule for Slice 1: all
   `SourceRange` offsets are BYTE offsets; scanning iterates bytes** (reuse
   `spipe_knowledge_provider/provider_utf8_decoder.spl` /
   `segmented_bytes.spl` patterns). Char-indexed `s[i]` never appears in the
   scanner. S1-A's spec includes a fixture doc with multibyte text before,
   inside, and after every link form, and asserts rewrite round-trips
   byte-identically outside the target range.
2. **COW alias mutation.** `val t = self.table; t.push(x); self.table = t`,
   `self.xs = f(self.xs, v)`, and `.keys()`/`.values()` inside a loop each
   deep-copy the whole collection per write. The reverse index and edge tables
   are exactly the shape this kills at repo scale (`doc/` is ~10⁵ files).
   Mutate through the single owner (`self.index[k].push(v)`), hoist `.keys()`
   above loops. `scripts/check/check-cow-alias-hotpath.shs` ratchets this.
3. **Nested closures can read but not modify outer vars** — scanner
   accumulators must be explicit state structs passed/returned, not captured
   `var`s.
4. **Chained methods on erased receivers** (from ANY/dict) fail mid-chain —
   graph code pulling records out of dicts must bind an intermediate typed
   `val` before chaining.
5. **Native-codegen Dict gaps still open:** `f64`-value `.get()` miss, and
   class-field `d[k]` bracket-read on array values (truth table in
   `doc/07_guide/language/dict_native_pitfalls.md`). The score engine holds
   `f64` per-scope values → key scores by struct field or int-scaled values
   (points in tenths as int), or consult the truth table before each op.
6. **`Result<T,E>` + `?` only** — no try/catch exists. Journal recovery is
   modeled as typed states, not exception unwinding.
7. **Seed version:** `admit`/`assume` as identifiers, `examples`/`and_then`/
   `move` as names require a seed ≥ 2026-08-21. Verify with
   `bin/simple --version` before starting; a parse error naming these tokens
   means stale binary, not wrong code.
8. **SSpec:** `describe` inside `fn main` exits 1 despite 0 failures — end
   specs with `return ()`. Every spec ships pass + mutation-red evidence.
9. **No inheritance**; generics `<>`; enums + traits + composition (§5).

---

## 4. REVISED WAVE PLAN

**Core value, per the brief: link safety + balance score + admission.**

### 4.1 CUT / DEFERRED (unchanged from revision 1, one delta)

W1 repo consolidation (defer, cross-repo); W2 skill compiler (cut from slice 1);
W5 logical mounts (cut, speculative); W6 pair experts (cut, most speculative);
W9 GitHub writer (cut; local read-only `admit` verdict only); W10 Leiden (cut);
W11 promotion (cut); W12 retirement (cut — but the *freeze* in §3.2 starts now);
W7 Semantic-purity/Stability/Reachability components (defer to slice 2 —
renormalized weights Cohesion 43 / Trace 21 / Shape 21 / Axis 15, originals
recorded in config); W8 optimizer reduced to proposal generator + dry-run,
`--apply` in slice 2. Rationale unchanged; see research doc for what each was.

**Delta:** revision 1's "MCP wiring" in S1-D is cut too. The JS MCP stub is 9
lines of nothing; a Simple MCP surface is slice 2, after the CLI proves the API.

### 4.2 Slice 1 — five packages, all pure Simple under `src/app/spipe/`

- **S1-E — Record model + identity (NEW package, was "already exists" in JS).**
  The Simple port of the model subset everything else needs.
- **S1-A — Link extraction + reverse index.**
- **S1-B — Link-safe move/rename transaction.**
- **S1-C — Balance score engine, advisory.**
- **S1-D — Diagnostics registry (SDN) + admission verdict + CLI entrypoint.**

---

## 5. PARALLELIZATION MAP — Slice 1

Root: `src/app/spipe/` (sources), `test/01_unit/app/spipe/` (specs),
`test/fixture/spipe/` (fixtures). **No two packages create or edit the same
file.** Shared files owned by exactly one package (⚑). All five start
immediately, with one sequencing rule the JS plan didn't need: A–D **import**
S1-E's types to compile at all, so S1-E's FIRST commit, on day one, is
`model/types.spl` containing exactly the §6 declarations (no logic). The other
four import it from the start — never write local copies of the structs — and
only their specs' green status waits on S1-E's remaining files (uid/edge/
canonical).

### S1-E — Record model + identity

**Creates**
- `src/app/spipe/model/types.spl` (⚑ ALL frozen types of §6 live here)
- `src/app/spipe/model/uid.spl` (canonical UID: SHA-256 + Crockford base32,
  ported from JS `model/identity.js`; reuse `std` sha256 / provider
  `streaming_sha256.spl` — no new hashing)
- `src/app/spipe/model/edge.spl` (edge construction, sort, endpoint validation;
  `EdgeType` enum with the 19 JS `EDGE_TYPES` incl. `links_to`)
- `src/app/spipe/model/canonical.spl` (canonical bytes — delegate to
  `spipe_knowledge_provider` canonical JSON emitter or SDN canonical form;
  pick one, document it, use it everywhere)
- `test/01_unit/app/spipe/model_identity_spec.spl`, `model_edge_spec.spl`
- `test/fixture/spipe/uid_vectors.sdn` (vectors generated once from the JS
  implementation; parity oracle per §3.2)

**Contract:** UIDs, edge sort keys, and canonical bytes are byte-compatible with
the JS implementation for the vector fixtures. Pure functions; no filesystem.

**Acceptance:** `bin/simple test test/01_unit/app/spipe/model_identity_spec.spl
test/01_unit/app/spipe/model_edge_spec.spl` green; every UID vector matches;
duplicate-edge-type and bad-endpoint constructions return `Err`.

### S1-A — Link extraction + reverse index

**Creates**
- `src/app/spipe/scan/regions.spl` (fenced-block + code-span byte ranges)
- `src/app/spipe/scan/links.spl` (link scanner → `LinkRecord`/`SourceRange`)
- `src/app/spipe/scan/headings.spl` (heading offsets + slugs + section UIDs)
- `src/app/spipe/graph/reverse_index.spl` (pure `build_reverse_index(edges)`)
- `test/01_unit/app/spipe/link_extraction_spec.spl`, `reverse_index_spec.spl`
- `test/fixture/spipe/slice1_links/` (MUST include multibyte-text fixtures, §3.5.1)

**Edits** none (types come from S1-E's frozen §6 shapes).

**Contract**
- Emits `links_to` edges via S1-E's edge constructor, `origin: explicit`,
  `status: accepted`; `from_uid` = enclosing section UID else artifact UID
  (matches JS `extract/trace.js:196` behavior).
- All offsets are byte offsets; byte-iteration only (§3.5.1).
- Reverse index is derived, never stored; rebuild-equals-incremental asserted.
- Owner-mutation only for the index dict (§3.5.2).
- Diagnostics from SPK110–129 only, exported as a `LINK_DIAGNOSTICS` table
  (const list in its own file); S1-D merges it.

**Acceptance:** `bin/simple test test/01_unit/app/spipe/link_extraction_spec.spl
test/01_unit/app/spipe/reverse_index_spec.spl` green; inline / reference-def /
reference-use / autolink found; links inside fences and code spans NOT found;
heading-anchor link resolves to section UID; multibyte fixture offsets verified
by slicing the raw bytes at the reported range and comparing to `raw_target`;
every found link also present in `std.common.markdown`'s parse (oracle check);
incremental rebuild equality on the fixture corpus.

### S1-B — Link-safe move/rename transaction

**Creates**
- `src/app/spipe/refactor/plan.spl` (`(edges, reverse_index, request) → RefactorPlan`)
- `src/app/spipe/refactor/rewrite.spl` (byte-range edits, descending offset)
- `src/app/spipe/refactor/journal.spl` (write-ahead journal in SDN;
  `planned → staged → applied → committed`; `rollback` from any pre-committed)
- `test/01_unit/app/spipe/refactor_rewrite_spec.spl`, `refactor_journal_fault_spec.spl`
- `test/fixture/spipe/slice1_refactor/`

**Edits** none. Never imports `scan/` — consumes `SourceRange` only.

**Contract**
- Rewrites only `[target_start, target_end)` bytes; everything else preserved
  byte-verbatim (this is what makes a structural commit semantically neutral).
- All fallible steps return `Result`; journal recovery is typed state replay,
  not exceptions. Fault injection = truncate/corrupt the journal at each state
  and re-open (§3.3), asserting corpus is fully-old or fully-new.
- Before/after hashes via S1-E `canonical.spl`; emits an `AliasRecord` per move.

**Acceptance:** both specs green via `bin/simple test
test/01_unit/app/spipe/refactor_rewrite_spec.spl
test/01_unit/app/spipe/refactor_journal_fault_spec.spl`; fault spec covers all
four transitions; property check: zero broken links after any accepted move on
the fixture corpus (re-scan with a fixture-local copy of expected edges);
multibyte round-trip byte-identical outside edited ranges.

### S1-C — Balance score engine (advisory)

**Creates**
- `src/app/spipe/balance/score.spl` (`score_scope`, `score_report`)
- `src/app/spipe/balance/components/{cohesion,trace_alignment,shape,axis_coverage}.spl`
- `src/app/spipe/balance/config.spl` + `src/app/spipe/balance/config.sdn`
  (thresholds from research §13.2/§13.4 as data; original 7-component weights
  recorded alongside the renormalized 43/21/21/15)
- `test/01_unit/app/spipe/balance_score_spec.spl`
- `test/fixture/spipe/slice1_balance/` (hand-built good/bad trees)

**Edits** none.

**Contract**
- Pure function of `(artifacts, edges, reverse_index, config)`. No filesystem,
  clock, or randomness — determinism is hard (research §3.4).
- **Points are int tenths** (`score: 824` = 82.4) end to end — sidesteps the
  native `f64` Dict gap (§3.5.5) AND makes cross-platform determinism trivial
  (no float summation order questions). Rendering divides at the edge.
- Every deduction carries an SPK51x code + evidence; no unexplained points.
  Never a hard error (hard integrity belongs to S1-A/S1-D).
- Component traits: each component implements trait
  `BalanceComponent { fn name() -> text; fn raw(input: ScopeInput) -> Int }`
  (raw in per-mille); score.spl composes them — no inheritance.

**Acceptance:** `bin/simple test test/01_unit/app/spipe/balance_score_spec.spl`
green; scoring twice yields identical canonical bytes; good fixture beats bad
on every component; a scope's score equals the sum of its own deductions'
arithmetic.

### S1-D — Diagnostics registry, admission verdict, CLI entrypoint

**Creates**
- `src/app/spipe/diagnostics/registry.sdn` (⚑ single code→meaning source of
  truth, SDN; includes ALL legacy JS codes as reserved rows)
- `src/app/spipe/diagnostics/registry.spl` (loader + duplicate check)
- `src/app/spipe/admission/verdict.spl` (pure:
  `(ScoreReport, [Diagnostic], Config) → AdmissionVerdict`, §13.4 thresholds)
- `src/app/spipe/main.spl` (⚑ CLI: `knowledge graph|links|score|admit` via
  `bin/simple run src/app/spipe/main.spl -- <cmd>`; `admit` exits 1 below the
  70.0 deny floor)
- `test/01_unit/app/spipe/diagnostics_registry_spec.spl`, `admission_verdict_spec.spl`

**Edits** none outside `src/app/spipe/` — deliberately does NOT touch the
shared `src/app/io/dispatch/table.spl` in Slice 1 (parallel-session contention;
promotion to a built-in `bin/simple` subcommand is a one-line slice-2 change).
Does not expose `rebalance`/`promote` (consistent with the released-surface
spec, though that spec binds only the JS CLI).

**Contract:** registry is the only place an SPK code is *defined*; S1-A/S1-C
export code tables that S1-D merges; registry spec fails on any duplicate code,
on any code used in `src/app/spipe/` but unregistered, and on any new code
outside the §2.1 free ranges.

**Acceptance:** `bin/simple test test/01_unit/app/spipe/diagnostics_registry_spec.spl
test/01_unit/app/spipe/admission_verdict_spec.spl` green;
`bin/simple run src/app/spipe/main.spl -- knowledge score test/fixture/spipe/slice1_balance/good`
prints a report and exits 0; `knowledge admit` on the bad fixture exits 1.

### Dependency order

```
S1-E freezes types (§6 is the spec; E is the code) ─┐
S1-A ──────────────┬────────────────────────────────┴─> edges + reverse index
                   ├─> S1-B
                   └─> S1-C ──> S1-D (verdict + CLI integration last)
```

All five start concurrently against §6; integration lands E → A → (B, C) → D.

---

## 6. FROZEN INTERFACES (Simple types — S1-E owns the code, this doc the spec)

Frozen for slice 1. A package needing a change files a request; no unilateral
edits. No inheritance anywhere; generics `<>`; enums for closed sets.

### 6.1 `SourceRange` + `LinkRecord` (S1-A → S1-B)

```simple
enum LinkForm:
    Inline
    ReferenceDefinition
    ReferenceUse
    Autolink

struct SourceRange:
    path: text           # canonical_path, POSIX separators
    start_offset: Int    # BYTE offset, >= 0, first byte of the whole link
    end_offset: Int      # BYTE offset, exclusive; > start_offset
    target_start: Int    # rewritable target substring within [start, end)
    target_end: Int      # exclusive
    link_form: LinkForm
    raw_target: text     # verbatim, pre-resolution, e.g. "../x/y.md#a-heading"
    fragment: Option<text>
```

Rule: S1-B rewrites only `[target_start, target_end)`. Offsets are bytes of the
raw file content as read — no NFC pre-normalization in slice 1 (the JS plan
normalized; rewriting must write back byte-identical non-target content, so the
scanner works on raw bytes; record as a difference from research §9).

### 6.2 `EdgeRecord` (S1-E)

```simple
enum EdgeOrigin: Explicit; Inferred; Trace
enum EdgeStatus: Accepted; Candidate; Rejected

struct EdgeRecord:
    uid: text                     # derived, model/uid.spl
    edge_type: EdgeType           # 19-variant enum incl. LinksTo — model/edge.spl
    from_uid: text
    to_uid: text
    origin: EdgeOrigin
    status: EdgeStatus
    source_range: Option<SourceRange>   # present on every LinksTo edge
```

### 6.3 `ScoreReport` (S1-C → S1-D) — points in int TENTHS

```simple
struct ComponentScore:
    name: text        # "cohesion" | "trace_alignment" | "shape" | "axis_coverage"
    weight: Int       # 43 / 21 / 21 / 15
    raw_permille: Int # 0..1000
    points_tenths: Int  # weight * raw_permille / 100, half-up

struct Deduction:
    code: text            # "SPK511"
    component: text
    points_tenths: Int
    evidence: sdn         # free-form SDN value: paths, counts, thresholds

struct ScoreReport:
    schema: text          # "spipe-balance/1"
    scope: text           # "" = global
    score_tenths: Int     # 0..1000; sum of components' points_tenths
    components: [ComponentScore]
    deductions: [Deduction]
    scopes: [ScoreReport] # children, depth-first, path-sorted
```

Canonical serialization via S1-E `canonical.spl`; field order as declared.

### 6.4 `AdmissionVerdict` (S1-D)

```simple
enum Verdict: Accept; AcceptWithDebt; Reject

struct AdmissionReason:
    code: text            # SPK530–549
    scope: text
    message_key: text
    details: sdn

struct Thresholds:        # research §13.4, tenths
    target: Int           # 850
    floor: Int            # 800
    deny: Int             # 700
    max_global_regression_tenths: Int   # 5
    max_scope_regression_tenths: Int    # 10
    legacy_required_improvement_tenths: Int  # 20

struct AdmissionVerdict:
    schema: text          # "spipe-admission/1"
    verdict: Verdict
    reasons: [AdmissionReason]
    thresholds: Thresholds
    hard_diagnostic_count: Int   # non-zero forces Reject
```

### 6.5 Diagnostics registry row (SDN, S1-D owns the file)

```sdn
diagnostic: {code: "SPK110", severity: error, message_key: "link_target_missing",
             component: link, owner: simple}
# legacy rows: owner: legacy_js, reserved forever (§2.1)
```

Severity: `error | warning | info`. Component: `link | balance | admission |
legacy`. Free ranges as §2.1 only.

### 6.6 Reused as-is — do not re-implement

- `src/app/spipe_knowledge_provider/`: `streaming_sha256.spl`,
  `canonical_json_emitter.spl`/`_decoder.spl`, `lexical.spl`,
  `provider_utf8_decoder.spl`, `segmented_bytes.spl`
- stdlib: `std` sha256 (`src/lib/common/crypto/sha256`), SDN read/write, path
  utils; `std.common.markdown` (as test oracle only)
- Legacy JS (`examples/05_stdlib/spipe/src/model/*`): read for porting + vector
  generation; never imported, never edited.

---

## 7. RECORDED DEBT (file these, do not silently absorb)

1. Link extraction is a byte-offset region-exclusion scanner, not a CommonMark
   AST (research §9.1). Preferred payoff: add source offsets + link nodes to
   `std.common.markdown`, then swap the scanner's core. Revisit on first
   fidelity bug.
2. `.spipe/spipe` (0.1.0) and `examples/05_stdlib/spipe` (0.2.0) are
   independently versioned writable copies. Cross-repo; untouched in slice 1.
3. Score components Semantic purity / Stability / Reachability unimplemented;
   renormalized weights with originals retained in `config.sdn`.
4. `REQ-SPKC-031` is a permanent numbering gap.
5. The JS knowledge core was never reachable from CLI/MCP; the Simple CLI (S1-D)
   supersedes rather than fixes this. JS package is feature-frozen (§3.2);
   retirement (research W12) unscheduled.
6. Graph store / snapshot store / retrieval stack exist only in JS; ported (or
   retired) on demand in later slices, with `GraphStore` cursor/limit semantics
   and the SPK7xx/8xx/9xx codes as the porting contract.
7. `main.spl` CLI is not yet a `bin/simple` built-in subcommand (deliberate —
   shared dispatch-table contention); promote in slice 2.
8. Slice 1 scans raw bytes without NFC normalization (differs from research §9);
   revisit if UID stability across differently-normalized checkouts bites.

---

## 8. SLICE 1 — LANDED 2026-08-31

All five packages implemented in pure Simple under `src/app/spipe/`. Verified in
one combined run (not five separate green reports):

```
bin/simple test test/01_unit/app/spipe/
Results: 73 total, 73 passed, 0 failed     (9 spec files, all outcome=OK)
```

Drift checks: **zero** re-declarations of the frozen types outside
`model/types.spl` — no package forked them. Every package reports pass +
mutation-red evidence.

### 8.1 Open seams (real work, not cosmetics)

1. ~~**Duplicate canonical encoders.**~~ **RESOLVED 2026-08-31.**
   `model/canonical.spl` gained `CDict([CanonicalField])` + `cfield()`, emitting
   fields in **byte-sorted** key order (`_key_less` over `.bytes()`, deliberately
   not `<` on `text`: char-oriented comparison can order non-ASCII keys
   differently per host, which is the exact failure this encoder exists to
   prevent). `balance/score.spl`'s local encoder is deleted and now builds a
   `CanonicalValue`; its public signature is unchanged. Both header comments were
   rewritten — the originals justified the fork by the *absence* of dict support,
   and leaving that text standing would have invited a third encoder.
   `model/canonical.spl` is now the ONE encoder; add new shapes there.
   New spec `test/01_unit/app/spipe/model_canonical_dict_spec.spl` (8 examples):
   sorted-not-construction order, byte-order sorting (`é` 0xC3 after `z` 0x7A),
   non-ASCII value round-trip, nesting, quote escaping in keys as well as values.
   Verified 8/8 + score 11/11 + identity 11/11 green; mutation-red by disabling
   the key sort → 4/8 fail; restored byte-identical.
   Settled in passing: `_json_escape`'s `while i < s.len()` + `substring(i, i+1)`
   is **not** a bytes/chars bug — the non-ASCII cases exercise that path directly
   and pass, so `len()` and `substring` agree here.
2. **S1-A ↛ S1-B integration.** S1-B started before `model/types.spl` existed and
   designed `plan.spl` around pre-resolved `FileRewrite`/`RewriteEdit` data, so it
   never imports the frozen types. S1-A produces a reverse index S1-B cannot yet
   consume. Wiring them is genuine work, not a rename.
3. **`bin/simple run <script> --` does not strip the `--` separator**
   (reported by S1-D, worked around by documenting "invoke without `--`";
   **not independently confirmed** — verify before filing). Per CLAUDE.md a
   broken short form gets fixed or filed, never normalized in a usage comment.
4. `config.sdn` is documentation-only; `config.spl` hardcodes the same numbers
   rather than parsing it. Two sources of truth for the weights.

### 8.2 Process finding for the next slice

The day-one-types sequencing **partly failed**: S1-E landed `model/types.spl`
first as designed, but S1-B and S1-C had already begun designing around its
absence (S1-C migrated onto it mid-flight; S1-B never did). Overlapping the model
package with its dependents does not work. Next slice: land the model package
alone, confirm it on disk, *then* fan out.

Corrected along the way: `Int` **is** a valid Simple type (638 files under
`src/` use it). An agent reported it invalid after hitting `cannot cast u8 to
Int` in byte-scanning context — a cast error, not a missing type. The plan's
`-> Int` signatures were correct as written.
