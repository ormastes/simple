# `src/lib/common/c_parser/` is specced by 56 system-test examples but has never existed (2026-08-04)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Found:** 2026-08-04

## 2026-08-10 re-verification

Re-confirmed, no code change: `ls src/lib/common/c_parser/` still
`No such file or directory`; `git log --oneline -- 'src/lib/common/c_parser'`
still returns nothing. This is unchanged from the original report — the
directory has never existed. The fix genuinely requires implementing a C
type model, a `#define`/preprocessor pass, and a C-name matcher as new
modules (a feature, not a bug fix), reconciled against the partial
`src/compiler/10.frontend/c_import/__init__.spl` model to avoid a duplicate
C type system — exactly as scoped below. Left honestly open; not attempted
this session (out of scope for a bug-triage lane, per the doc's own "Why not
fixed now" section).
**Class:** specced-but-unimplemented. 56 failing examples across three specs in
`test/03_system/compiler/`.

## Symptom

```
FAIL  test/03_system/compiler/c_parser_spec.spl        (0 passed, 35 failed)
FAIL  test/03_system/compiler/import_c_defines_spec.spl (2 passed, 17 failed)
FAIL  test/03_system/compiler/import_c_match_spec.spl  (10 passed,  4 failed)
```

Every failing example is a source-presence assertion against a path that does
not exist:

```
$ ls src/lib/common/c_parser/
ls: cannot access 'src/lib/common/c_parser/': No such file or directory
```

The specs read three files there via `rt_file_read_text(path) ?? ""`, so a
missing file yields `""` and every `src.contains(...)` assertion fails:

| spec | file it reads |
|------|---------------|
| `c_parser_spec.spl:16` | `src/lib/common/c_parser/c_types.spl` |
| `import_c_defines_spec.spl:17` | `src/lib/common/c_parser/c_preprocessor.spl` |
| `import_c_match_spec.spl:17` | `src/lib/common/c_parser/c_name_match.spl` |

## Root cause (what is PROVEN)

1. **The directory has never existed in this repository's history.**
   `git log --oneline -- 'src/lib/common/c_parser'` returns nothing, and
   `find src -path '*c_parser*' -name '*.spl'` finds only the unrelated
   `src/app/wrapper_gen/spec_parser.spl`. So this is not a refactor that moved
   files — it is an implementation that never landed. These specs have been red
   since the day they were written.

2. **This is NOT the same defect as the sibling stale-path family.**
   `bitfield_reorder_spec.spl` failed the same way but its target code *does*
   exist, just relocated into `_Attributes/`, `_TypeLayout/` and `_Items/`
   submodules; that spec was repaired by repointing it. Here there is nothing to
   repoint to.

3. **A partial, differently-shaped C model exists elsewhere and is not a
   substitute.** `src/compiler/10.frontend/c_import/__init__.spl` defines
   `CField`, `CStruct`, `CEnum` and friends, but the shapes diverge from what
   the spec requires — e.g. the spec asserts `CField` carries
   `array_size: i32` (`c_parser_spec.spl:15,21`) and the in-tree `CField` has
   only `name`, `c_type`, `is_pointer`, `bit_width`. There is no
   `c_preprocessor` (`#define` handling) and no `c_name_match` module anywhere
   in `src/` — `grep -rl 'c_preprocessor\|CTypeKind\|c_name_match'` over
   `src/**/*.spl` returns zero files.

4. **Silent-empty read is what turns "missing module" into 56 opaque assertion
   failures.** The helper is `fn read_text(path) -> text: rt_file_read_text(path) ?? ""`.
   A nonexistent path is indistinguishable from an empty file, so the operator
   sees 35 `expected false to equal true` lines instead of one "file not found".

## Why not fixed now

Making these green requires **implementing a C parser library** — a C type
model, a `#define`/preprocessor pass, and a C-name matcher — as three new
modules under `src/lib/common/c_parser/`, with shapes reconciled against the
partial `c_import` model already in the frontend so the repo does not end up
with two divergent C type models (the duplication hazard recorded repeatedly in
this tracker). That is a feature, not a bug fix, and it is far outside a
test-repair lane.

Two smaller follow-ups worth doing independently of the feature:

- **Make the missing-file case loud.** `read_text` swallowing a missing path
  into `""` should instead fail the example with the path in the message. Three
  specs in `test/03_system/compiler/` share this exact helper.
- **Decide the shape question first.** If the intended home for the C type model
  is `src/compiler/10.frontend/c_import/`, then these specs should be repointed
  there and their extra assertions (`array_size`, the preprocessor, the name
  matcher) filed as the real feature gaps — rather than a second parallel
  library being written under `src/lib/common/`.

## Verification 2026-08-17 (content classification, fleet lane I)
STILL-OPEN. `ls -d src/lib/common/c_parser` -> No such file or directory.
`test/03_system/compiler/c_parser_spec.spl` is still present and still imports
the absent library. The 56 system-test examples remain specced against nothing.
Not fixable in this lane: this is "implement a C parser library", a feature, not
a defect repair.
