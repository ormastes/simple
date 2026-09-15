# 67 spec files never parse, so they run zero examples — and the suite calls that fine

- **Status:** 2 repaired (99 examples recovered, all green), 65 remaining,
  frozen by a ratchet. NOT fixed wholesale — see "Why not just fix all 67".
- **Found:** 2026-09-13, while triaging AVX/SIMD spec failures
- **Gate:** `scripts/check/check-orphaned-docstring-tail.shs`
  + `scripts/check/orphaned_docstring_baseline.txt`

## The defect

A documentation pass appended a section to many `.spl` files:

    ## Compatibility and limitations
    Executed on the interpreter test lane; asserts observable values only ...
    """

with **no opening `"""`**. The bare closer is parsed as CODE, so the file does
not compile. In `avx2_fp_emit_spec.spl` the prose line then reached the parser
as an expression and `on` demanded a pointcut:

    parse: Unexpected token: expected pointcut expression 'pc{...}',
           found Identifier { name: "the" }

The same edit also **ate the file's `use` line**. That matters: repairing only
the docstring made the file parse and then fail every example with
`function emit_vaddps_ymm not found`. Both halves had to be restored.

## Why this is worse than 67 broken files

A spec that cannot parse asserts nothing and is indistinguishable, in a suite
summary, from a spec with no findings. `.claude/rules/testing.md` already names
this trap — "a scan that finds nothing may have scanned nothing" — and this is
that trap at suite scale. These files were not reported as failures. They were
not reported at all.

`avx2_fp_emit_spec.spl` (51 examples) and `fma3_emit_spec.spl` (48) were
**99 AVX2-FP and FMA3 encoder examples that had never executed**. Once
repaired, all 99 pass on the first run: the encoders in
`encode_x86_64_avx2_fp.spl` and `encode_x86_64_fma3.spl` were correct the whole
time, and the byte-level VEX encoding they pin — the thing an AVX lane most
needs pinned — was unguarded.

## Repaired here

| spec | examples | before | after |
|---|---|---|---|
| `test/01_unit/compiler/backend/avx2_fp_emit_spec.spl` | 51 | parse error, 0 run | 51/51 |
| `test/01_unit/compiler/backend/fma3_emit_spec.spl` | 48 | parse error, 0 run | 48/48 |

Repair recipe, both halves required:

1. Replace the orphaned tail with a comment block (`# Compatibility and
   limitations` / `# <prose>`). The content is documentation and the file has
   no module-docstring slot left at that point.
2. Restore the `use` line by deriving it from the symbols the spec calls — for
   these two the called set matched the module's `export` list exactly, 8 for 8.

## Why not just fix all 67

Step 1 is mechanical. **Step 2 is not** — the correct import depends on which
symbols each spec calls, and a spec that parses can then fail for real reasons,
as these two did until their imports were restored. Landing 65 newly-parsing
files without checking each would convert a silent hole into a loud one and
bury the genuine reds among them. Each needs its own repair and its own run.

The 67 are enumerated in `scripts/check/orphaned_docstring_baseline.txt`.

## The gate

`check-orphaned-docstring-tail.shs` is a RATCHET, not a zero-bar: the backlog
exists, so a fatal zero-bar would block every push. It fails on a NEW
occurrence, and equally on a **stale baseline** — a listed file that has been
repaired must be removed from the list, because a baseline that no longer
describes the tree is how a ratchet silently stops ratcheting.

Detection is an odd number of `"""` OCCURRENCES (not lines — a one-line
docstring carries two on one line and is balanced) plus a bare closer two lines
under a column-0 `## Heading`. `build/` is pruned: it holds untracked COPIES of
the source tree, which otherwise report the same defect dozens of times under
paths nobody can repair. `vendor/` is out of scope per CLAUDE.md.

`--selftest` runs first and is fatal: a must-flag fixture of the real shape, a
one-line docstring and a balanced multi-line docstring that must NOT flag, and
a copy under `build/` that must be pruned. Verified live in both directions —
a planted offender gives `FAIL — ... NEW`, and a baselined path that no longer
matches gives `FAIL — ... STALE`.

Measured: `PASS — 44161 file(s) scanned, 0 new, 0 stale (67 baselined)`, 65s.

## Note on the count

An earlier, looser census (any unbalanced `"""`) found 185 files. That is a
SUPERSET and includes false positives — sampling showed a file with unbalanced
quotes that still parses. The 67 are those matching the exact docgen-tail
signature; 2 of 3 sampled from the looser set failed to parse, so the true
population of unparseable `.spl` files is somewhere between 67 and 185 and has
not been established. Establishing it needs a parse of every file, which is a
separate piece of work.
