# `MirToLlvm` no longer satisfies `MirTextCodegen` — blocks EVERY spec on main

**Status:** FIXED — verified stale as of 2026-08-05 (see "2026-08-05 verification" below)
**Found:** 2026-08-04
**Severity:** blocks the entire test lane, not one backend
**Owner:** whoever is driving the bootstrap "by index" refactor — this is
diagnosis only, deliberately not patched (see "Why this is not fixed here")

## 2026-08-05 verification

Reproduced the exact repro command from this doc verbatim:

```
bin/simple test test/01_unit/lib/common/arch_spec.spl
```

Result: **exit 0**, last output line is `Results: 27 total, 27 passed, 0
failed`. No `translate_block` / `MirTextCodegen` / "does not implement
required method" text anywhere in the (captured, full) output. The trait
error described in this doc does not reproduce.

Root cause confirmed via `git log --oneline -- src/compiler/70.backend/backend/common/mir_text_codegen.spl`:
two same-day fix commits landed after this doc was filed:

- `4670db2d31f2c36fc2378998de6e5be9adb16f03` (2026-08-04T09:02:24+00:00)
  "fix(backend): sync MirTextCodegen required methods with index-based
  dispatch" — renamed the trait's declared `translate_block` /
  `translate_terminator` / `translate_call` to the by-index forms
  (`translate_block_at` / `translate_terminator_at` / `translate_call_at`)
  that `MirToLlvm` actually implements, i.e. exactly the fix path this doc
  already diagnosed (mechanical adapter for the first four methods) but
  chose not to land.
- `f4a4703f0fb9f493880c21fbb710b173c8936c58` (2026-08-04T09:20:28+00:00)
  "fix(backend): give MirTextCodegen.translate_function its real 3-arg
  signature" — a related arity mismatch on `translate_function` (2-arg
  trait decl vs 3-arg `MirToLlvm` impl / call sites), found because the
  interpreter's trait-conformance check only compares method **names**
  (`interpreter_eval.rs:985`), never arity/param/return types.

The doc's "last two ([`translate_stub`, `translate_unsupported`]) are the
interesting part... never implemented by this backend" observation checked
out as accurate but not blocking: `src/compiler/70.backend/backend/common/mir_text_codegen.spl`
lines 281–285 give both methods trivial default bodies (`me
translate_stub(...): ()` / `me translate_unsupported(...): ()`) directly on
the trait, so `MirToLlvm` satisfies the trait via the default and never
needs to override them. `grep` confirms 0 occurrences of either name in
`src/compiler/70.backend/backend/_MirToLlvm/*.spl` even after the fix —
consistent with the doc, not contradicting it.

This session (2026-08-05) additionally ran dozens of unrelated `bin/simple
test <spec>` commands earlier today, all producing real `Results:` lines —
independent corroboration that the "blocks EVERY spec" condition no longer
holds on this checkout. Original diagnosis content below is left intact as
history; only the Status line and this section were added.

## Symptom

Any `bin/simple test <spec>` aborts before the runner executes anything:

```
error: semantic: type `MirToLlvm` does not implement required method
       `translate_block` from trait `MirTextCodegen`
```

Fix that one and the next missing method surfaces — the checker reports one at
a time.

## Blast radius: global, not x25519

Reproduced on `test/01_unit/lib/common/arch_spec.spl`, which has nothing to do
with the x25519mlkem768 campaign or with crypto: exit 1, no `Results:` line,
same error as the last line. A parallel run of 5 campaign specs x 2 different
compiler binaries produced this same abort in all 10 runs. It is not a timeout
(exit 1 with a real diagnostic, not 143/255) and not a parse failure (0 hits for
`Dedent`, `parse:`, `Failed to load` in every log).

Present on origin/main at both `6b7f7f634d9` and `d6a15f0e21b`, so it has
survived at least two pushes.

## Exact gap: 5 methods

The impl is spread across `src/compiler/70.backend/backend/_MirToLlvm/`
(`core_codegen.spl`, `class_def.spl`, `aggregate_intrinsics.spl`,
`asm_constraints_helpers.spl`) — 94 `me` methods total, with the single
`impl MirTextCodegen for MirToLlvm:` at `core_codegen.spl:153`. Against the 59
methods required by `common/mir_text_codegen.spl`, exactly five are unsatisfied:

| required method | status |
|---|---|
| `translate_block(block: MirBlock)` | renamed to `translate_block_at(blocks, block_index)` |
| `translate_terminator(term: MirTerminator)` | renamed to `translate_terminator_at(...)` |
| `translate_instruction(inst: MirInst)` | renamed to `translate_instruction_at(...)` |
| `translate_call(dest: LocalId?, func, args)` | renamed to `translate_call_at(...)` |
| `translate_stub(dest: LocalId, name: text)` | **never implemented** — 0 occurrences in the directory |
| `translate_unsupported(inst: MirInst)` | **never implemented** — 0 occurrences in the directory |

The first four are collateral from the by-index refactor
(`6b7f7f634d9` "translate terminators by block index", `0ae43f73ac9`,
`0005061fe47`, and siblings), which renamed this backend's methods to take
`(collection, index)` instead of a value.

**The last two are the interesting part**: they have *never* been implemented by
this backend, so the trait was already unsatisfied before the refactor. That
means the trait requirement itself, or its enforcement, changed — the rename is
what made it visible, not the whole cause. Whoever owns this should establish
that first; patching only the four renames will just move the error to
`translate_stub`.

The sibling backends are unaffected and still define the value-taking form:
`_CBackendTranslate/class_core.spl:233`, `lua_backend.spl:156`,
`wat_codegen.spl:201,206`. No caller anywhere dispatches `translate_block` on
`MirToLlvm`.

## Why this is not fixed here

A mechanical adapter is available for the four renames — e.g.
`me translate_block(block): self.translate_block_at([block], 0)`, which is exact
rather than approximate because `translate_block_at` reads only
`blocks[block_index]` and never looks at sibling blocks. I wrote it, confirmed
it satisfied that method, and then **reverted it**: it does not unblock anything
on its own (the error simply advances to `translate_terminator`), and the
remaining two require inventing semantics for stub/unsupported lowering inside a
subsystem another session is actively refactoring. Landing four guessed adapters
plus two invented methods into an in-flight refactor is how parallel sessions
clobber each other.

## Reproduce

```
bin/simple test test/01_unit/lib/common/arch_spec.spl
# exit 1; last line is the trait error; no Results: line
```

Score the **last line**, not the exit code — the log is thousands of lines of
`[gc-warning]` noise first.
