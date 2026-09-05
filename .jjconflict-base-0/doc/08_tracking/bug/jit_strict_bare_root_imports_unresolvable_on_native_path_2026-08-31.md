# 342 `SIMPLE_JIT_STRICT` suite failures — root cause: a stray tracked `test/01_unit/lib/src/` poisons project-root detection

Filed 2026-08-31. **Root cause CORRECTED 2026-08-31 (same day).** Status: OPEN,
fix in flight on `fix/cov-wrapper-import-resolution`.

> **Filename notice.** The path still says `bare_root_imports_unresolvable_on_native_path`.
> That was the *retracted* hypothesis. The path is retained deliberately so the
> cross-references in PR #169 and the retraction below stay resolvable. Read the
> title, not the filename.

---

## RETRACTION — what this record originally claimed, and why it was wrong

The first version of this record claimed the root cause was a **global gap in the
module resolver**: that bare source roots (`os.`, `common.`, `lib.`,
`nogc_sync_mut.`) had no mapping on the native/HIR path, and that consequently
**~11,000 import sites** would need re-pointing. It recommended a reviewed change
to `module_resolver/resolution.rs`.

**That root cause is retracted. It is wrong.** So is the ~11,000-site conclusion
drawn from it. (The 11,000 *census* is still an accurate count of bare-root
import sites; it simply is not a count of broken ones, and nothing needs
re-pointing.)

### The reasoning error, left legible on purpose

The retracted conclusion rested on this A/B:

```
use std.os.crypto.blake2b.{blake2b}  → simple compile → rc=0
use os.crypto.blake2b.{blake2b}      → simple compile → rc=1
```

Both forms name the same file, so the split looked like proof that the bare form
had no mapping. It was not. **The A/B varied the import spelling but held the
file's location fixed**, and location was the actual variable:

- `use std.*` routes through the **stdlib-root** strategy, which does not consult
  `source_root` and therefore dodges the corruption entirely.
- `use os.*` routes through **Strategy 4** (`source_root/<seg0>`), which does.

Run anywhere inside the poisoned subtree, those two strategies produce exactly
the rc=0 / rc=1 split observed. The observation was real and reproducible; the
inference from it was not. A single-variable experiment was needed and a
two-variable one was run.

The record also reported that the spec "fails `compile` in-tree too", offered as
evidence against a tmp-copy artifact. That observation is still true, but it was
over-read: it ruled out `/mnt/data/tmp` specifically while leaving *every other*
location-dependent explanation standing — including the real one.

---

## Actual root cause

A stray **tracked** directory `test/01_unit/lib/src/` (plus siblings under
`test/{01_unit,unit}/lib/{gc,nogc}_*/src/`, **44 files** total) poisons project-root
detection.

`module_resolver/types.rs:394 find_project_root` walks ancestors and returns the
first one containing a `src/` directory. For any spec under `test/01_unit/lib/**`
that ancestor is `test/01_unit/lib` itself, so:

- project root becomes `test/01_unit/lib`
- `source_root` becomes `test/01_unit/lib/src`
- Strategy 4 (`source_root/<seg0>`) can no longer reach the real `src/os`,
  `src/lib/common`, …

Hence `cannot resolve import` for `os.*`, `common.*`, etc. — but **only inside
that one subtree**.

## Discriminating evidence (verified independently in a detached worktree at `origin/main`)

**1. Same import, two locations — the single-variable experiment.**

| file | import | rc |
|---|---|---|
| `test/tmpprobe/a.spl` | `use os.crypto.blake2b.{blake2b}` | **0** |
| `test/01_unit/lib/crypto/zz_probe.spl` | *byte-identical* | **1** |

Identical source, identical spelling; only the directory differs. A global
bare-root gap cannot produce this.

**2. Move the poison away and back — flips in both directions**, recompiling the
**unmodified** `blake2_rfc7693_kat_spec.spl` at its real in-repo path:

```
poison present:    rc=1
poison moved away: rc=0      # mv test/01_unit/lib/src /mnt/data/tmp/...
poison restored:   rc=1
```

**3. Containment.** 466 of 466 specs with `cannot resolve import` on `origin/main`
are under `test/01_unit/lib/`; **zero** outside it. A global resolver gap would
fail everywhere.

Credit: root cause found by the sibling agent on the `cannot resolve import`
class; independently reproduced here (all three flips above) before this
correction was written.

---

## Findings that SURVIVE the correction

These were established independently of the retracted root cause and remain
valid.

### `SIMPLE_JIT_STRICT` is not an env gate for this class

Nobody set `SIMPLE_JIT_STRICT`. For the `cannot resolve import` class,
`driver/src/exec_core.rs:1457-1465` returns a string that merely **reuses** the
`SIMPLE_JIT_STRICT:` prefix, with **no env-var check at all**. The genuinely
env-gated branch is further down at `:1486`. The code comment gives the reasoning:
an import naming a nonexistent module can never be satisfied by de-JITing — it
only defers the failure to the first call, surfacing as an unrelated "function
not found".

The escape hatch for this class is `SIMPLE_ALLOW_UNRESOLVED_IMPORTS=1`
(`hir/lower/module_lowering/module_pass.rs:43`). **Do not set it in any lane** —
it restores warn-and-continue and re-hides the defect.

### The serious branch is ruled out

All 342 occurrences are the single `cannot resolve import` class. **Zero** are
tail-return corruption, receiver-mutation, or cross-module private-symbol
collision. The `$dupN` collision text appears in the suite log only as
*warnings*, never among the failures. The silent-wrong-dispatch worry does not
apply here.

### The gate is working correctly

Verdict **(a)** stands, on a corrected causal story. The suite binary was built
from exactly `b0be388ec46` (#157), which made a non-compiling coverage wrapper an
ERROR instead of a silent pass. These specs previously reported PASS. #157 did
its job; what it exposed was the poisoned project root, not a resolver gap.

### Distribution (unchanged)

339 distinct specs: `test/01_unit/lib/common` 275, `.../lib/crypto` 24,
`.../lib/nogc_sync_mut` 14, `.../lib/hardware` 10, others 16 — all inside the
poisoned subtree, consistent with the containment evidence above.

---

## Fix

In flight on **`fix/cov-wrapper-import-resolution`** (sibling agent). The
direction is to remove/relocate the 44 stray tracked files so no `src/` dir sits
above a spec, and/or harden `find_project_root` so a `src/` under `test/` cannot
be mistaken for a project root.

**Do not** attempt the retracted `module_resolver/resolution.rs` bare-root change.
There is nothing to fix there.

## Related

Four sibling branches work other coverage-wrapper failure classes and are
unrelated to this one: `fix/cov-wrapper-hir-lowering` (#164),
`fix/cov-wrapper-optional-lteq` (#156), `fix/cov-wrapper-rbracket-val` (#155),
`fix/cov-wrapper-undefined-identifiers` (#163).

Original (retracted) filing: PR #169.
