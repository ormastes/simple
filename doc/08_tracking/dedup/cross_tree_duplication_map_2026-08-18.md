# Cross-Tree Stdlib Duplication Map (2026-08-18)

Audit-only. Systematic map of file-path duplication across the three parallel
stdlib trees `src/lib/nogc_sync_mut/`, `src/lib/nogc_async_mut/`,
`src/lib/gc_async_mut/`, produced as evidence for future dedup tranches
(goal 7). No source was refactored to produce this report.

## Method

1. `find` each tree, strip the tree-root prefix, sort — three relative-path
   lists.
2. Relative-path intersection (`comm -12`) pairwise across the three trees,
   unioned: **2,207** relative paths exist in 2 or more trees.
3. For each such path: `md5sum` every present copy. All-sums-equal =>
   `IDENTICAL`. Otherwise pairwise `diff`, ratio = `(changed lines) /
   max(line count)` over the worst pair. `< 10%` => `NEAR`, else
   `DIVERGENT`.

## Summary counts

| class | count | % of 2,207 |
|---|---|---|
| IDENTICAL (byte-identical, all present copies) | 434 | 19.7% |
| NEAR (<10% line-diff ratio, worst pair) | 794 | 36.0% |
| DIVERGENT (>=10% line-diff ratio) | 979 | 44.3% |
| **Total paths present in >=2 trees** | **2,207** | 100% |

Identical files by which tree-set holds them:

| tree-set | count |
|---|---|
| `nogc_sync_mut` + `nogc_async_mut` + `gc_async_mut` (all 3) | 209 |
| `nogc_sync_mut` + `nogc_async_mut` only | 220 |
| `nogc_async_mut` + `gc_async_mut` only | 4 |
| `nogc_sync_mut` + `gc_async_mut` only | 1 |

The dominant pattern is `nogc_sync_mut` <-> `nogc_async_mut` identity (429 of
434 identical files include this pair) — consistent with `http/url.spl` and
`buffer/utilities.spl` precedent.

## Top 20 largest identical files (by line count) + mergeability verdict

Verdict methodology: a file is **mergeable-candidate** if its `use`/`import`
lines (first ~6, checked directly) name no tree-specific facility (no
`nogc_async_mut`/`gc_async_mut`/GC/actor/generator-specific modules) and the
file itself does not implement a tree-differentiated wrapper. Files with zero
`use`/`import` lines are leaf/pure-logic and default mergeable pending a
closer read. This is a **candidate list**, not a merge decision — each entry
still needs the closer-read pass described in Method step 2 of the task
before any move.

| lines | path | tree-set | imports (evidence) | verdict |
|---|---|---|---|---|
| 744 | `amqp_utils.spl` | sync+async+gc (all 3) | none found | mergeable-candidate (pure logic) |
| 724 | `df/mod.spl` | sync+async | none found | mergeable-candidate |
| 699 | `allocator.spl` | all 3 | none found | mergeable-candidate — verify no raw-pointer/GC-tier divergence by full read (name suggests memory-tier sensitivity) |
| 649 | `debug/formats/test/macho_roundtrip_spec.spl` | sync+async | test fixture | mergeable-candidate (test-only) |
| 648 | `debug/formats/test/.spipe_matchers_macho_roundtrip_spec.spl` | sync+async | generated matcher file | mergeable-candidate (generated, regen not merge) |
| 637 | `src/testing/mocking_advanced.spl` | all 3 | none found | mergeable-candidate |
| 634 | `net/http.spl` | all 3 | `use std.error.*`, `use std.net.sffi.*` | mergeable-candidate — sffi import is a leaf module, not tree-specific |
| 616 | `net/telnet.spl` | all 3 | `use std.error.*`, `use std.net.tcp.*`, `use std.common.string_core.*` | mergeable-candidate |
| 616 | `debug/formats/dwarf_parser.spl` | sync+async | none found | mergeable-candidate |
| 540 | `file_system/utilities.spl` | sync+async | not checked | needs read |
| 527 | `lsp/handlers/verification.spl` | all 3 | `import lsp.protocol`, `import lsp.transport`, `use compiler.treesitter.*`, `import io.fs` | needs read — imports app-layer modules, not obviously tree-neutral |
| 516 | `debug/formats/test/golden_elf_dwarf_spec.spl` | sync+async | test fixture | mergeable-candidate (test-only) |
| 515 | `debug/formats/test/.spipe_matchers_golden_elf_dwarf_spec.spl` | sync+async | generated matcher file | mergeable-candidate (generated) |
| 500 | `diagram/__init__.spl` | sync+async | not checked | needs read |
| 491 | `lsp/handlers/completion.spl` | all 3 | not checked | needs read (sibling of verification.spl above) |
| 479 | `src/testing/mocking_async.spl` | all 3 | not checked — name implies async-tier semantics | **likely identical-by-coincidence, not by necessity** — flag for read; "async" in the name is suspicious for a file also duplicated verbatim in `nogc_sync_mut` |
| 479 | `message_transfer.spl` | all 3 | `use memory.refc_binary.*`, `use types.*` | needs read — refc_binary may be tier-specific |
| 478 | `src/testing/mock/verification.spl` | all 3 | `import testing.mock.builder.*` | mergeable-candidate |
| 473 | `engine/physics/joints.spl` | sync+async | not checked | needs read |
| 463 | `net/__init__.spl` | all 3 | `use std.net.tcp.*`, `use std.error.*`, `use std.net.udp.*` | mergeable-candidate |

## Constraint on any merge plan

**`doc/08_tracking/bug/import_triggered_cross_module_symbol_misdispatch_2026-08-18.md`**
documents that adding/moving `use`/`import` lines can trigger cross-module
symbol misdispatch. Any tranche that relocates a file to a shared owner
(e.g. under `src/lib/common/`) and re-points three `use` sites at it must
treat that re-pointing as import-graph surgery, not a pure move — verify
against that bug's repro shape before landing, and re-run the affected
trees' tests, not just the moved file's own test.

## Recommended next tranche (max 5, safest first)

Ordered by risk (lowest first): test-only fixtures and generated files first
(no runtime import-graph exposure), then pure-logic leaf files with zero
`use` lines, then files with only leaf-module (`std.*`) imports.

1. **`debug/formats/test/macho_roundtrip_spec.spl`** + its paired
   `.spipe_matchers_macho_roundtrip_spec.spl` (649+648 lines, sync+async
   identical) — test-only, no production import-graph exposure.
2. **`debug/formats/test/golden_elf_dwarf_spec.spl`** + its paired
   `.spipe_matchers_golden_elf_dwarf_spec.spl` (516+515 lines, sync+async
   identical) — same rationale.
3. **`amqp_utils.spl`** (744 lines, identical across all 3 trees, zero
   `use`/`import` lines found) — pure logic, largest single-file win.
4. **`net/telnet.spl`** (616 lines, all 3 trees, only `std.error`/`std.net.tcp`/
   `std.common.string_core` leaf imports) — precedent-consistent with
   `net/http.spl`.
5. **`src/testing/mock/verification.spl`** (478 lines, all 3 trees, only
   `testing.mock.builder` import) — mirrors the already-deduplicated
   `http/url.spl` pattern (test-support module, narrow import surface).

Explicitly deferred pending a closer read (do not include in the next
tranche): `lsp/handlers/verification.spl` / `completion.spl` (app-layer
imports, unclear tier-neutrality), `src/testing/mocking_async.spl` (name
suggests tier-specific semantics despite being byte-identical — needs
content read, not just import-line read), `message_transfer.spl` (imports
`memory.refc_binary`, plausible tier sensitivity), `allocator.spl` (name
implies memory-tier sensitivity despite zero external imports — verify
no inline tier-conditional logic before treating as mergeable).

## Tranche 1 execution attempt (2026-08-18)

Re-verified byte-identity for all 5 recommended tranche-1 targets — all
confirmed still `IDENTICAL` across every tree that holds them (md5sum, all
copies match):

- `debug/formats/test/macho_roundtrip_spec.spl` (sync+async) — identical.
- `debug/formats/test/.spipe_matchers_macho_roundtrip_spec.spl` (sync+async) — identical.
- `debug/formats/test/golden_elf_dwarf_spec.spl` (sync+async) — identical.
- `debug/formats/test/.spipe_matchers_golden_elf_dwarf_spec.spl` (sync+async) — identical.
- `amqp_utils.spl` (all 3 trees) — identical, 95 top-level `fn` (all
  `create_*`/`frame_*`-prefixed AMQP 0-9-1 frame builders).
- `net/telnet.spl` (all 3 trees) — identical.
- `src/testing/mock/verification.spl` (all 3 trees) — identical.

**No source was moved or merged in this pass.** Searched the tree for the
merge shape the map's own "Constraint" section pointed at
(`grep -rl "goal-7 dedup"`): the only prior goal-7 dedup landing found is
`http/url.spl`, and it is **not** a whole-file move-to-`common`-plus-thin-
delegate. Each of the 3 `http/url.spl` copies is still a full, independent
259-line file; only two small leaf helpers (`to_hex`/`from_hex`) were
factored out to call `std.common.binary_inspect.{percent_hex_encode_byte,
percent_hex_decode_pair}` in-place. There is **no existing precedent
anywhere in the tree** for the "move whole file to `src/lib/common/`, make
each tree copy a thin delegating module" shape this tranche's instructions
describe as "whatever the established pattern is" — that pattern does not
exist yet, so choosing it here would be inventing new import-graph shape,
not following one, directly against the caution in
`doc/08_tracking/bug/import_triggered_cross_module_symbol_misdispatch_2026-08-18.md`.

Given that:
1. A full per-symbol collision grep against everything importable from
   `src/lib/common/` (95 functions for `amqp_utils.spl` alone, plus
   `net/telnet.spl` and `verification.spl`) was not completed this pass —
   each name needs a tree-wide grep before a move can be called safe, and
   that work was not finished.
2. The test-spec pairs (items 1-2) are not really "mergeable" in the sense
   the rest of tranche 1 is: they are duplicate test suites that each
   exercise their OWN tree's (identically duplicated but separately owned)
   `debug/formats/dwarf_parser.spl` / macho fixtures. Collapsing the spec
   files to one location without also collapsing the module under test
   would either drop coverage of one tree's copy silently or require the
   test runner to resolve a spec against multiple trees, which is outside
   this tranche's scope (`dwarf_parser.spl` was NOT one of the 5 targets).

## Tranche 2 (2026-08-18) — `net/telnet.spl` and `src/testing/mock/verification.spl`

Precedent used: `ce7b330b911` (`amqp_utils.spl` -> `src/lib/common/amqp_utils.spl`,
3 tree copies replaced with a 5-line `pub use std.common.amqp_utils*`
delegator; sample read from `src/lib/nogc_sync_mut/amqp_utils.spl`).

There are actually **4** lib trees on disk (`nogc_sync_mut`, `nogc_async_mut`,
`gc_async_mut`, `gc_sync_mut`), not 3 — `gc_sync_mut` was silently excluded
from every prior "all 3 trees" byte-identity claim in this doc. Re-verified
by md5sum:

- `net/telnet.spl`: `nogc_sync_mut` / `nogc_async_mut` / `gc_async_mut` all
  `604fcfe0...` (identical); `gc_sync_mut` is `19a3bd81...` (**different**).
- `src/testing/mock/verification.spl`: `nogc_sync_mut` / `nogc_async_mut` /
  `gc_async_mut` all `a3db08cd...` (identical); `gc_sync_mut` is
  `6171dde8...` (**different**). So "all 3 trees" in the earlier entries was
  correct as far as it went — it just never mentioned the 4th, non-matching
  tree exists.

### 1. `net/telnet.spl` — SKIP (tree-specific import found)

Its 3 `use` lines: `std.error.{SimpleError, error}`,
`std.net.tcp.{TcpStream}`, `std.common.string_core.{bytes_to_text}`.
`std.error` and `std.common.string_core` do resolve to
`src/lib/common/error.spl` / `src/lib/common/string_core.spl` — genuinely
tree-neutral. But `std.net.tcp` does **not** live under `src/lib/common/` at
all — `net/tcp.spl` exists only as 4 separate per-tree files
(`src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/net/tcp.spl` at
`f70b1c37...`, `src/lib/gc_sync_mut/net/tcp.spl` at `d16f6184...`, itself the
same 3-identical-plus-1-different split as telnet.spl). A `std.X` prefix does
not imply tree-neutrality here: `std.net.tcp` resolves per-tree via each
tree's own search root, so a copy of `telnet.spl` moved into
`src/lib/common/` would have no `net/tcp.spl` sibling to resolve against.
This is exactly the `std.<tier>.*`-shaped hazard the task called out, just
disguised as `std.net.tcp` instead of `std.nogc_sync_mut.net.tcp`. **SKIP —
not moved.**

### 2. `src/testing/mock/verification.spl` — SKIP (tree-specific import found)

Its only import: `import testing.mock.builder: CallRecord, MockFunction,
Expectation, VerificationResult`. `builder.spl` is the same shape again —
`src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/src/testing/mock/builder.spl`
all `39179f9e...` (identical), `src/lib/gc_sync_mut/.../builder.spl` is
`2e2e1802...` (different) — and none of the 4 copies live under
`src/lib/common/` (confirmed: `find src/lib/common -iname '*testing*' -o
-iname '*mock*'` returns nothing under `src/lib/common` for this path).
Moving `verification.spl` to common would leave its `import
testing.mock.builder` line unresolvable from the common root. **SKIP — not
moved.**

Both targets fail the import-audit step of the per-file protocol before
reaching the collision-check or move steps, so no collision count, caller
count, or test run was performed for either — the protocol is fail-closed on
import audit alone. No files were changed, no commit was made for tranche 2.

**Status: all 5 targets DEFERRED, not merged.** No regression risk was
introduced (zero files changed). Re-verified-identical is recorded above so
a future pass does not need to redo step (a). Recommended before attempting
an actual merge: (i) establish and document a real "thin delegate" shape by
doing ONE whole-file case end-to-end with full collision-check + 3-tree spec
run, since none exists as precedent today; (ii) for the test-spec pairs,
decide the intended coverage semantics (shared spec vs. per-tree spec)
before treating them as a dedup target at all.

## Tranche 2 correction (goal 7, 2026-08-18) — `testing/mock/builder.spl` merged; `net/tcp.spl` still blocked

The tranche-2 SKIP on `src/testing/mock/verification.spl` was caused by
`verification.spl`'s own `import testing.mock.builder: ...` line, not by
`builder.spl` itself. **`builder.spl` has zero `use`/`mod`/`import` lines** —
it never actually needed the deferral, and the earlier tranche-2 entry above
should be read as "builder.spl's *dependent* is blocked", not "builder.spl is
blocked". This pass re-audited `builder.spl` in isolation and merged it:

- md5sum (re-confirmed, unchanged from tranche 2): `nogc_sync_mut` /
  `nogc_async_mut` / `gc_async_mut` all `39179f9e...` (identical);
  `gc_sync_mut` is `2e2e1802...` (**different — left untouched**, per the
  4-tree correction below).
- Import audit: zero `use`/`mod`/`import` lines in `builder.spl` itself — passes.
- Collision check: 14 top-level public symbols (`CallRecord`, `MockFunction`,
  `Expectation`, `VerificationResult`, `MockBuilder`, `RegistryEntry`,
  `MockRegistry`, `create_mock`, `MockPolicy`, `mock_policy_init`,
  `mock_policy_is_enabled`, `mock_policy_allow_in_layer`,
  `mock_policy_disable`, `mock_policy_reset`) checked against every
  `fn`/`struct`/`enum`/`class`/`val`/`trait` definition under
  `src/lib/common/` — **0 collisions**.
- Moved to `src/lib/common/testing/mock/builder.spl` (311 lines, unchanged;
  `src/lib/common/` uses flat topic dirs with no `src/` prefix, so the mirror
  drops the tree-side `src/` segment). The 3 identical tree copies
  (`nogc_sync_mut`, `nogc_async_mut`, `gc_async_mut`) replaced with a 5-line
  `pub use std.common.testing.mock.builder*` delegator, same comment style as
  the `amqp_utils.spl` precedent (`ce7b330b911`). `gc_sync_mut`'s copy is
  untouched — it already carries its own divergent content (a
  `gc_async_mut`-forwarding compat facade), so it stays exactly as-is; no
  normalization was applied to it.
- Callers: `grep -rn 'mock\.builder\|mock/builder' src/ test/ --include='*.spl'`
  found real importers only against the `nogc_sync_mut` tree path
  (`use std.nogc_sync_mut.src.testing.mock.builder.{MockFunction}` in
  `test/01_unit/lib/std/testing/prevention_mock_spec.spl`,
  `test/01_unit/compiler/di/di_lock_spec.spl`,
  `test/unit/compiler/di/di_lock_spec.spl`,
  `test/01_unit/app/devhub/adapter_bitbucket_spec.spl`), plus same-tree
  relative importers inside each of the 3 merged trees
  (`mock/spy.spl`, `mock/prevention.spl`, `mock/verification.spl`,
  `testing/mocking_core.spl`'s `mod mock.builder`) — none of those needed
  edits, since the delegator file stays at the same per-tree path and
  re-exports the same symbol names.
- Verification: ran the 3 pre-existing real specs that exercise the
  `nogc_sync_mut` delegator directly — `prevention_mock_spec.spl`
  (`Results: 6 total, 6 passed, 0 failed`), `di_lock_spec.spl`
  (`Results: 15 total, 15 passed, 0 failed`), `adapter_bitbucket_spec.spl`
  (`Results: 65 total, 65 passed, 0 failed`) — all unchanged/green. No
  pre-existing spec exercises the `nogc_async_mut` or `gc_async_mut`
  delegators directly, so a throwaway spec
  (`test/01_unit/lib/std/testing/mock_builder_delegator_throwaway_spec.spl`,
  resolving `MockFunction` through each of those two tree paths) was written,
  run (`Results: 2 total, 2 passed, 0 failed`), and deleted.

Net line delta: -933 (three 311-line duplicates removed) + 311 (common owner)
+ 15 (three 5-line delegators) = **-607 lines**, zero behavior change on the
3 merged trees, `gc_sync_mut` untouched, zero regression.

**`net/tcp.spl` remains SKIPPED, unchanged from the tranche-2 entry above** —
it has a genuine per-tree-only import (`std.net.tcp` has no
`src/lib/common/` sibling for any of the 4 trees) and was explicitly out of
scope for this pass (no further recursion attempted).

**4-tree correction applied to the recommended list:** any future dedup pass
over this doc's earlier "3 tree copies" language must read it as "3 of 4
trees, `gc_sync_mut` excluded and checked separately" — `gc_sync_mut`
frequently diverges (own content, or its own compat facade forwarding
elsewhere) and must never be silently folded into a byte-identity claim or
normalized into a shared delegator; only trees that are byte-identical are
merged, and a diverging 4th copy is left exactly as it was.

## Precedent established (2026-08-18, goal 7)

`amqp_utils.spl` is now the first landed whole-file cross-tree dedup: content
moved to `src/lib/common/amqp_utils.spl` (744 lines, unchanged), and each of
the 3 tree copies (`nogc_sync_mut/`, `nogc_async_mut/`, `gc_async_mut/`)
replaced with a 5-line delegator:

```
# AMQP (Advanced Message Queuing Protocol) 0-9-1 Utilities
# Delegator: real implementation lives in src/lib/common/amqp_utils.spl
# ...
pub use std.common.amqp_utils*
```

Protocol followed, fail-closed at every step:
- Re-verified byte-identical via `md5sum` (all 3 still matched).
- Confirmed zero `use`/`mod` lines in the source file.
- Collision-checked all 161 top-level `fn`/`struct`/`enum`/`val` names
  (95 `fn`, rest `val` protocol constants) against every definition in
  `src/lib/common/` — **0 collisions**, so the
  `import_triggered_cross_module_symbol_misdispatch_2026-08-18.md` hazard
  (duplicate public symbol + added import flips resolution) does not apply
  here.
- Callers: `grep -rn amqp_utils src/ test/ --include='*.spl'` found **zero**
  real importers anywhere in the tree (only a doc concatenation file
  mentions the old path) — this file was dead code with no import-graph
  exposure, which is why it was the safest possible first case.
- Verification: no existing spec touches `amqp_utils` (`grep -rl amqp
  test/` empty), so a throwaway spec per tree
  (`use std.amqp_utils.{FRAME_METHOD, CLASS_BASIC}`,
  `use std.nogc_async_mut.amqp_utils...`,
  `use std.gc_async_mut.amqp_utils...`) was written under `test/01_unit/`,
  run via `bin/simple test`, confirmed `Results: 1 total, 1 passed, 0
  failed` for all three delegator paths, then deleted (throwaway, not
  committed).

Net line delta: -2187 (three 744-line duplicates removed) + 744 (common
owner) + 15 (three 5-line delegators) = **-1428 lines**, zero behavior
change, zero regression.

This establishes the "move whole file to `src/lib/common/`, thin
`pub use module*` delegator per tree" shape as real precedent — the shape
described but never before landed (see "Tranche 1 execution attempt"
above). Still open for a future tranche: this file's zero-caller,
zero-collision profile is unusually favorable and should not be assumed to
generalize — every other tranche-1 candidate still needs its own full
collision check before being moved the same way.

## Raw data

Full per-file classification (2,207 rows: class, path, diff metric, tree-set)
was generated by a one-off shell script during this audit and not committed
(intermediate artifact, not a project deliverable). Re-run via the Method
above to regenerate if a future tranche needs the complete table rather than
just the top 20.

## src/testing/mock/verification.spl — BLOCKED on a symbol collision (2026-08-18)

Import blocker RESOLVED: its only import, `testing.mock.builder`, now lives at
`src/lib/common/testing/mock/builder.spl` (merged in `764913af784`), and
common-tree files resolve sibling dotted paths the same way (verified against
`src/lib/common/crypto/tls12_prf.spl`'s `mod crypto.types`).

md5: nogc_sync_mut = nogc_async_mut = gc_async_mut = `a3db08cdc32b388f94a57abbaab72324`;
gc_sync_mut = `6171dde8ab43a8f81c71bf89df8f5ae7` (divergent, excluded per the 4-tree rule).

**Blocker: `class Matcher` collides.** Defined in BOTH
`src/testing/mock/verification.spl:20` (mock arg matcher, `matches_fn: fn(text) -> bool`,
methods any/eq/gt/lt/contains/…) and `src/lib/common/contract.spl:187` (Pact-style
contract matcher, fields `match_type/example/regex`). Unrelated types, same name.
Moving verification.spl into `common` puts both in one flat namespace — the exact
shape of `doc/08_tracking/bug/import_triggered_cross_module_symbol_misdispatch_2026-08-18.md`.

Merge stays blocked until one of them is renamed (a deliberate API decision, not a
dedup side effect). The other 21 public symbols were collision-free.
