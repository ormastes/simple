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

## Tranche 3 (goal 7, 2026-08-18) — `src/testing/mocking_advanced.spl` merged; `allocator.spl` considered

Selection method: re-ran md5sum on every remaining top-20 candidate not yet
merged/blocked (`df/mod.spl`, `allocator.spl`, `src/testing/mocking_advanced.spl`,
`debug/formats/dwarf_parser.spl`), confirming there are actually 4 lib trees
(`nogc_sync_mut`, `nogc_async_mut`, `gc_async_mut`, `gc_sync_mut`) and only the
first 3 needed to match:

| path | nogc_sync_mut | nogc_async_mut | gc_async_mut | gc_sync_mut |
|---|---|---|---|---|
| `df/mod.spl` | `af8b3cc1...` | `af8b3cc1...` (match) | missing | missing |
| `allocator.spl` | `eb033d44...` | `eb033d44...` (match) | `eb033d44...` (match) | `7093108b...` (divergent) |
| `src/testing/mocking_advanced.spl` | `67821e44...` | `67821e44...` (match) | `67821e44...` (match) | `1d0cca8b...` (divergent) |
| `debug/formats/dwarf_parser.spl` | `b224da7e...` | `b224da7e...` (match) | missing | missing |

`allocator.spl` and `mocking_advanced.spl` both have 3-way matches (safer:
more copies collapsed) and zero `use`/`mod`/`import` lines in the source
(`grep -nE '^(use|mod|import)'` on each returned nothing). `df/mod.spl` and
`dwarf_parser.spl` only exist in 2 trees each — lower impact, deferred, not
examined further this pass.

### Accepted: `src/testing/mocking_advanced.spl` (637 lines)

- Import audit: zero `use`/`mod`/`import` lines — passes.
- Collision check: 14 top-level public symbols (`TaskPriority`,
  `ScheduledTask`, `TaskScheduler`, `BackoffStrategy`, `RetryAttempt`,
  `RetryPolicy`, `RateLimiter`, `TimeoutResult`, `TimeoutController`,
  `ExecutionEvent`, `ExecutionOrderTracker`, `ConcurrencyController`,
  `Debouncer`, `Throttler`) grepped against every
  `fn`/`struct`/`enum`/`class`/`val`/`trait` definition under
  `src/lib/common/` — **0 collisions**.
- Moved to `src/lib/common/testing/mocking_advanced.spl` (637 lines,
  unchanged). The 3 identical tree copies (`nogc_sync_mut`, `nogc_async_mut`,
  `gc_async_mut`) replaced with a 6-line `pub use
  std.common.testing.mocking_advanced*` delegator, same comment style as the
  `testing/mock/builder.spl` precedent (`764913af784`). `gc_sync_mut`'s copy
  (`1d0cca8b...`) is untouched — genuinely divergent content, no
  normalization applied.
- Callers: `grep -rln mocking_advanced src/ test/ --include='*.spl'` found
  only same-tree relative importers — `use testing.mocking_advanced.*` in
  each tree's own `src/testing/mocking.spl`, plus a comment mention in
  `src/testing/__init__.spl`. No test spec references it directly
  (`grep -rln mocking_advanced test/` empty), so a throwaway spec
  (`test/01_unit/lib/std/testing/mocking_advanced_delegator_throwaway_spec.spl`,
  instantiating `RetryPolicy.new(3)` through all 3 delegator paths via
  `std.nogc_sync_mut.src.testing.mocking_advanced`,
  `std.nogc_async_mut.src.testing.mocking_advanced`,
  `std.gc_async_mut.src.testing.mocking_advanced`) was written, run
  (`Results: 1 total, 1 passed, 0 failed`), and deleted (throwaway, not
  committed).

Net line delta: -1911 (three 637-line duplicates removed) + 637 (common
owner) + 18 (three 6-line delegators) = **-1256 lines**, zero behavior
change, zero regression. Commit: see `refactor(dedup)` commit for this
target.

### Deferred: `allocator.spl` (699 lines)

Not merged this pass. Its symbol names (`Allocator`, `SystemAllocator`,
`ArenaAllocator`, `PoolAllocator`, `SlabAllocator`, `sys_malloc`, `sys_free`,
`sys_realloc`, `ptr_is_null`, `ptr_write`, `ptr_read`, `buffer_offset`,
`memory_copy`, `align_up`, `is_aligned`, `next_power_of_2`,
`is_power_of_2`) show **0 collisions** against `src/lib/common/` by the same
grep, and the file itself has zero `use`/`mod` lines. But a broad
`grep -rln allocator src/ test/ --include='*.spl'` returns dozens of hits
(mimalloc*, gc.spl, rc.spl, ecs/entity.spl, gpu engine sessions, etc.) that
were not individually triaged into "actually imports this file" vs.
"mentions the word allocator/Allocator in an unrelated type/comment" within
this pass's time budget — the map's own caution ("name suggests memory-tier
sensitivity") means this file needs the closer per-caller read the protocol
requires before a move, not just a symbol-collision grep. Left as a
concrete next-pass target: re-run the caller grep, keep only lines with an
actual `use`/`import` of this file's dotted path, then apply the same
merge protocol.

## Tranche 4 (goal 7, 2026-08-18) — `engine/physics/joints.spl` and `diagram/__init__.spl` merged

Selection: re-verified md5sum for every remaining top-20 candidate not yet
merged/blocked/rejected (`net/http.spl`, `net/__init__.spl`,
`file_system/utilities.spl`, `lsp/handlers/completion.spl`,
`engine/physics/joints.spl`, `diagram/__init__.spl`, `df/mod.spl`,
`message_transfer.spl`) and checked the actual resolution target of every
`use`/`import` line (not just whether the name starts with `std.`) — this is
the exact check that tripped up `net/tcp.spl` in tranche 2.

**Rejected this pass, with evidence:**

- `net/http.spl` (`27db0254...`, sync=async=gc_async, gc_sync
  `a36bcf35...` divergent) — imports `use std.net.sffi.{...}`. Checked
  `net/sffi.spl` directly: it is **4 genuinely different per-tree files**
  (`1f7a9de0.../9fdd1d55.../f22521d2.../7e6ca979...`, no `src/lib/common/net/sffi.spl`
  sibling). Same per-tree-only-import hazard as `net/tcp.spl` in tranche 2,
  just disguised behind `std.net.sffi` instead of `std.net.tcp`. The map's
  earlier "sffi import is a leaf module, not tree-neutral" verdict (line ~60
  of this doc) was **wrong** — corrected here. SKIP.
- `net/__init__.spl` (`a7c9a6c1...` sync=async=gc_async, gc_sync
  `a1dc6b84...` divergent) — imports `std.net.tcp`, `std.net.udp`,
  `std.net.http`, `std.net.sffi`, all four per-tree-only (confirmed
  `net/tcp.spl` per tranche 2, `net/sffi.spl` above). SKIP.
- `df/mod.spl` (`af8b3cc1...`, sync=async only, missing from
  gc_async_mut/gc_sync_mut) — imports `use std.ndarray.*`. `ndarray/` is a
  directory present separately in all 4 trees
  (`src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut,gc_sync_mut}/ndarray`),
  with no `src/lib/common/ndarray` sibling — same per-tree-only hazard. SKIP.
- `message_transfer.spl` (`d9814988...` sync=async=gc_async, gc_sync
  `178b5893...` divergent) — imports `use memory.refc_binary.{...}` and
  `use types.{...}`. Neither resolves inside any of the 3 matching trees:
  `memory/refc_binary.spl` exists **only** under
  `src/lib/nogc_async_mut_noalloc/memory/refc_binary.spl` (a 5th tree, not
  one of the 3 that hold this file), and bare `types.spl` is missing from
  `nogc_sync_mut` entirely (`find` returns it only under `nogc_async_mut`,
  `gc_async_mut`, `common`, `crypto/`, `editor/`). The import graph for this
  file does not resolve cleanly and was not further triaged (its 4 real
  callers are `src/app/interpreter/memory/*`, a distinct file of the same
  name, not these lib copies) — left DEFERRED, not SKIP, pending a closer
  read of how these copies actually get loaded.
- `lsp/handlers/completion.spl` (`2e8f2ec6...` sync=async=gc_async, gc_sync
  `734d2dc6...` divergent) — imports `lsp.protocol`, `lsp.transport`,
  `compiler.treesitter`, all app-layer. Not re-examined further this pass
  (matches the map's original "needs read — app-layer imports" caution);
  left DEFERRED.
- `file_system/utilities.spl` (`5117d312...`, sync=async only) — is a
  re-export hub (`mod file_system.types/file_ops/dir_ops/path_ops/metadata`,
  5 sibling modules), not a standalone leaf; moving it requires moving or
  verifying all 5 siblings too. Not attempted this pass; left DEFERRED.

### Accepted: `engine/physics/joints.spl` (473 lines, sync+async only)

- md5sum: `nogc_sync_mut` = `nogc_async_mut` = `7abec735c675b3fdf25f2f6e536e2462`.
  Not present in `gc_async_mut` or `gc_sync_mut` (2-tree duplication, not 3/4).
- Import audit: one import, `use std.common.math.{math_sqrt}` — resolves to
  `src/lib/common/math.spl`, already a common-owned leaf module (precedent:
  several existing `src/lib/common/*.spl` files already self-import via
  `use std.common.*`, e.g. `src/lib/common/cave_ca.spl`,
  `src/lib/common/base_encoding.spl` — confirmed this pattern works for a
  file that itself lives under `common`). Passes.
- Collision check: 11 top-level public symbols (`JointId`, `BodyRef`,
  `JointForce`, `DistanceJoint`, `RevoluteJoint`, `PrismaticJoint`,
  `SpringJoint`, `WeldJoint`, `JointType`, `JointEntry`, `JointRegistry`)
  grepped against every `fn`/`struct`/`enum`/`class`/`val`/`trait`
  definition under `src/lib/common/` — **0 collisions**.
- Moved to `src/lib/common/engine/physics/joints.spl` (473 lines, unchanged).
  The 2 identical tree copies (`nogc_sync_mut`, `nogc_async_mut`) replaced
  with a 5-line `pub use std.common.engine.physics.joints*` delegator, same
  comment style as the `testing/mock/builder.spl` precedent (`764913af784`).
  `gc_async_mut`/`gc_sync_mut` never had this file — nothing to touch there.
- Callers: `grep -rln 'physics.joints\|engine\.physics\.joints'` found
  `test/01_unit/app/io/rapier2d_ffi_spec.spl`,
  `test/03_system/engine/physics_joints_spec.spl`, plus mirrored copies
  under `test/unit/` and `test/system/` (pre-existing test-tree
  duplication, not touched).
- Verification (real specs, no throwaway needed):
  - `bin/simple test test/03_system/engine/physics_joints_spec.spl` ->
    `Results: 8 total, 8 passed, 0 failed`.
  - `bin/simple test test/01_unit/app/io/rapier2d_ffi_spec.spl` ->
    `Results: 1 total, 1 passed, 0 failed`.
  - Additionally wrote/ran/deleted a throwaway spec
    (`test/01_unit/lib/std/dedup_throwaway/joints_diagram_delegator_throwaway_spec.spl`)
    importing `std.nogc_async_mut.engine.physics.joints.{JointId}` to
    directly exercise the `nogc_async_mut` delegator (the two real specs
    above only reach the `nogc_sync_mut` copy) -> `Results: 2 total, 2
    passed, 0 failed` (this run combined the diagram check too — see below).
    Deleted before commit, not committed.

Net line delta: -946 (two 473-line duplicates removed) + 473 (common owner)
+ 10 (two 5-line delegators) = **-463 lines**, zero behavior change, zero
regression.

### Accepted: `diagram/__init__.spl` (500 lines, sync+async only)

- md5sum: `nogc_sync_mut` = `nogc_async_mut` = `45b31b2eef5e1a0708235e5fde9cae7c`.
  Not present in `gc_async_mut` or `gc_sync_mut` (2-tree duplication).
- Import audit: zero `use`/`mod`/`import` lines — passes (pure logic, a
  documented "stub implementation for test compatibility").
- Collision check: 17 top-level public symbols (`CallType`, `CallEvent`,
  `CallEventRecorder`, `record_call`, `record_return`, `DiagramConfig`,
  `_matches_pattern`, `_get_participant`, `_filter_events`,
  `SequenceGenerator`, `generate_sequence`, `to_mermaid_sequence`,
  `ClassDiagramGenerator`, `generate_class_diagram`, `to_mermaid_class`,
  `ArchDiagramGenerator`, `generate_arch_diagram`, `to_mermaid_arch`)
  grepped against every `fn`/`struct`/`enum`/`class`/`val`/`trait`
  definition under `src/lib/common/` — **0 collisions**.
- Moved to `src/lib/common/diagram/__init__.spl` (500 lines, unchanged). The
  2 identical tree copies (`nogc_sync_mut`, `nogc_async_mut`) replaced with a
  4-line `pub use std.common.diagram*` delegator, same comment style as
  precedent. `gc_async_mut`/`gc_sync_mut` never had this file.
- Callers: `grep -rln` for diagram usage found real production importers
  (`src/compiler_rust/lib/std/src/diagram/integration.spl`,
  `src/compiler_rust/lib/std/src/spec/diagram_integration.spl` — both Rust-seed
  mirror paths, out of scope for this `src/lib` merge) and 4 real spec
  families under `test/01_unit/lib/std/diagram/`
  (`recorder_spec.spl`, `sequence_gen_spec.spl`, `class_gen_spec.spl`,
  `arch_gen_spec.spl`), each mirrored under `test/unit/`.
- Verification: ran all 4 real spec files against the merged `nogc_sync_mut`
  delegator. **Pre-existing baseline failures were separately confirmed by
  temporarily restoring each tree copy to its `HEAD` (pre-merge) content,
  re-running, and diffing the `Results:` line** — every failure below is
  identical before and after the merge, so none is attributable to this
  change:
  - `recorder_spec.spl`: `Results: 24 total, 24 passed, 0 failed` (before
    and after — clean).
  - `sequence_gen_spec.spl`: `Results: 18 total, 17 passed, 1 failed`
    (before AND after — pre-existing, unrelated failure, unaffected by the
    delegator).
  - `class_gen_spec.spl`: `Results: 14 total, 11 passed, 3 failed` (before
    AND after — pre-existing).
  - `arch_gen_spec.spl`: `Results: 17 total, 15 passed, 2 failed` (before
    AND after — pre-existing).
  - Throwaway spec (see joints section above) additionally confirmed
    `std.nogc_async_mut.diagram.{CallType}` resolves through the
    `nogc_async_mut` delegator (the 4 real specs above only reach the
    `nogc_sync_mut` copy) -> included in the `Results: 2 total, 2 passed, 0
    failed` throwaway run. Deleted before commit.

Net line delta: -1000 (two 500-line duplicates removed) + 500 (common
owner) + 8 (two 4-line delegators) = **-492 lines**, zero *new* failures
(4 pre-existing sequence/class/arch failures reproduced identically on
`HEAD`, unrelated to this merge — see
`doc/08_tracking/bug/` for future filing if not already tracked).

**Tranche 4 total net line delta: -463 + -492 = -955 lines** across the 2
merged targets.

Files touched (absolute paths):
- `/mnt/data/worktrees/simple-main/src/lib/common/engine/physics/joints.spl` (new)
- `/mnt/data/worktrees/simple-main/src/lib/nogc_sync_mut/engine/physics/joints.spl` (delegator)
- `/mnt/data/worktrees/simple-main/src/lib/nogc_async_mut/engine/physics/joints.spl` (delegator)
- `/mnt/data/worktrees/simple-main/src/lib/common/diagram/__init__.spl` (new)
- `/mnt/data/worktrees/simple-main/src/lib/nogc_sync_mut/diagram/__init__.spl` (delegator)
- `/mnt/data/worktrees/simple-main/src/lib/nogc_async_mut/diagram/__init__.spl` (delegator)
- `/mnt/data/worktrees/simple-main/doc/08_tracking/dedup/cross_tree_duplication_map_2026-08-18.md` (this section)
