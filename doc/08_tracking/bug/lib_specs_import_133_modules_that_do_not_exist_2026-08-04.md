# 199 lib specs fail on 133 `std.*` modules that exist nowhere in the tree

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
**Found:** 2026-08-04
**Severity:** medium — these are not broken tests, they are tests for code that
was never written; they cost a red suite and hide the specs that fail for a
real reason

## Symptom

A spec whose only problem is a missing import fails as a single opaque failure,
because the file never loads:

```sh
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache test/01_unit/lib/math/bignum/bignat_spec.spl
  FAIL  test/01_unit/lib/math/bignum/bignat_spec.spl (0 passed, 1 failed)
        Error: error: semantic: Cannot resolve module: std.math.bignum.limb
Results: 1 total, 0 passed, 1 failed
```

Expected: 36 examples run. Actual: `1 failed`. The failure count understates
the loss by a factor of 36, and the message names the module rather than the
feature, so the cluster does not read as a cluster.

## Root cause

133 distinct `std.*` module paths imported by specs under `test/01_unit/lib/`
and `test/unit/lib/` resolve to no file or directory anywhere under `src/`.

Method (both passes are in the session scratchpad and rerunnable):

1. Collect every `^use std.<path>` from all 5,168 specs in scope — 1,758
   distinct module paths.
2. For each, strip a trailing Capitalized segment (that is a symbol import, not
   a module) and search all of `src/` for a matching `.spl` file **or**
   directory. 133 match nothing.
3. Grep the scope for specs importing any of the 133: **199 spec files**.

Confirmation the method is not over-reporting: the pass flagged
`math.bignum.limb`, `math.bignum.bignat`, `math.bignum.fixed`, and
`common.math.field.fe25519`, and all four were in fact absent. Implementing
them this session took `test/01_unit/lib/math/` from

```
Results: 9 total, 3 passed, 6 failed      # before
Results: 94 total, 92 passed, 2 failed    # after
```

— 85 examples that had never run. Both remaining failures are
`common.math.field.fe_p256`, also on this list. Note the "total" column: it
counts 9 before and 94 after, because a spec that fails to load contributes 1,
not its example count.

Distribution by feature area (module count, not spec count):

| area | missing modules |
|---|---|
| game2d | 20 |
| blink (browser) | 19 |
| hardware (rv64gc_rtl / soc_rtl) | 11 |
| database (sql, vector) | 11 |
| editor | 10 |
| fs / fs_driver (nvfs) | 11 |
| cc (compositor) | 7 |
| game3d | 5 |
| compression (brotli/gzip/lz4/zlib) | 5 |
| common (incl. `math.field.fe_p256`) | 5 |
| others (io, dap, debug, tls, ml, skia, signature, …) | 29 |

The shape is not scattered rot: it is whole feature areas specced ahead of
implementation. `game2d`, `blink`, `nvfs`, and the RV64 RTL model each account
for a double-digit block, and within a block the specs are internally
consistent — they were written against a design, not against code.

## Why not fixed now

Each block is a feature to implement, not a defect to repair, and they are
independent of each other — so this wants to be triaged into per-area lanes
(with the owning team deciding whether the spec or the plan is still current)
rather than fixed as one change. Several blocks are also in areas under active
development by other sessions right now (blink html_tree_builder, the GPU/
DrawIR renderer, editor), where landing a competing implementation would
conflict.

Two things would make the cluster visible without implementing anything, and
are worth doing first:

- **Report the loss honestly.** A load failure counts as `1 failed` no matter
  how many examples the file holds. The runner knows the example count from the
  manifest; reporting "0 of 36 ran" instead of "1 failed" would stop 199 files
  from looking like 199 small problems.
- **Fail the import at the right altitude.** `Cannot resolve module:
  std.math.bignum.limb` names a leaf. Naming the spec's whole unresolved import
  set at once would have made the 133/199 shape obvious from a single run.

## The same gap one level down: 347 symbols, in modules that DO exist

The module-level count is the floor, not the total. Repeating the scan at
symbol granularity — every `use std.<module>.{a, b, c}` in scope, flattened
across multi-line import blocks — gives 7,897 module/symbol pairs. Cross-
checking each name against every top-level declaration anywhere in `src/`
(155,828 distinct `fn`/`struct`/`enum`/`class`/`trait`/`val`/… names):

**347 distinct symbols are declared nowhere in `src/`**, spread over **432
module/symbol pairs in 191 modules that exist and load fine.** By grep, 279
spec files in `test/01_unit/lib/` name at least one of them (an upper bound —
a symbol name can appear coincidentally).

Worked examples, both verified by hand:

- `common.compress.utilities` — 21 absent symbols. The module is real
  (`src/lib/common/compress/utilities.spl`, 166 lines) but holds only option
  constructors and a CRC helper. The specs import a whole SIMD copy layer from
  it — `append_bytes_range`, `append_literal_copy`,
  `append_self_overlap_copy_{scalar,avx2,neon,for_tier}` — and
  `grep -rn 'fn append_self_overlap_copy_scalar' src/` returns nothing.
- `common.yaml` — `yaml_spec.spl` imports `yaml_get_scalar_content`,
  `is_yaml_null`, `is_yaml_boolean`, `is_yaml_sequence`, `is_yaml_mapping`,
  `yaml_get_sequence_items`, `yaml_get_mapping_pairs` from it. None exist, and
  neither does that module path (the real one is `std.common.encoding.yaml`).
  The seven names imply a *node*-based YAML model; the module that does exist
  is text-based (`yaml_parse -> (text, any)`, `yaml_parse_mapping -> list`).
  This is not a missing accessor set, it is a second YAML representation that
  was specced and never built — hence filed, not implemented.

This granularity matters for triage: a missing *module* reads as "that feature
does not exist yet", whereas a missing *symbol in a live module* looks like a
small gap and is repeatedly mistaken for one. Some genuinely are small — the
`chacha20_poly1305_seal`/`_open` pair fixed this session was exactly this
shape and took a thin wrapper over the existing verified core. Most are not.

## Re-verification 2026-08-09

Status confirmed **ARCHITECTURAL-OPEN** (this is a feature-completeness gap,
not a defect with a code fix).

- The doc's own headline "Symptom" repro module,
  `src/lib/common/math/bignum/{limb,bignat,fixed}.spl`, already exists on
  disk — it was implemented in the same original 2026-08-04 session per the
  doc's own "Root cause" section, and this pass confirms the files are
  present (this worktree has no deployed `bin/simple` to re-run the spec
  suite directly, per known worktree-isolation limits, so re-execution was
  not attempted; file presence is the honest check available here).
- The remaining claim — 133 distinct `std.*` module paths across whole
  feature areas (game2d, blink, hardware RTL, database, editor, nvfs, etc.)
  that were specced ahead of implementation — is not something this pass can
  responsibly reduce: each block is an independent feature (some actively
  owned by other concurrent sessions per the doc's own "Why not fixed now"),
  and building any of them out is out of scope for a bug-doc verification
  pass. No new code written against this doc this pass; it correctly remains
  OPEN and triaged as "implement per-feature-area", not "fix".

## Related

- `doc/08_tracking/bug/fe_p256_field_module_missing_2026-08-04.md` — the one
  entry on this list with a written-up API and a performance constraint.
- `doc/08_tracking/bug/app_modules_referenced_by_specs_exist_nowhere_2026-08-04.md`
  and `doc/08_tracking/bug/c_parser_library_specced_but_never_implemented_2026-08-04.md`
  — the same failure mode under `test/01_unit/app/`, found independently the
  same day. The pattern is tree-wide, not a `lib/` quirk.

## Re-triage 2026-08-17 (content-classified, m9a_tests lane)

**Verdict: LIVE BUT MASSIVELY OVERSTATED — magnitude re-measured.**

Re-resolved every `use std.X` in every `.spl` under `test/**/lib/**` against
`src/lib/` **and its five family subdirectories** (`common/`,
`nogc_sync_mut/`, `nogc_async_mut/`, `gc_async_mut/`,
`nogc_async_mut_noalloc/`). The original count was produced by a resolver that
did not search the family subdirectories, so it counted resolvable modules as
missing (`std.spec` and `std.spipe` alone accounted for 2,623 phantom misses).

| metric | doc claim | measured 2026-08-17 |
|---|---|---|
| std imports scanned | — | 9,228 |
| distinct unresolved `std.*` modules | 133 | **24** |
| lib test files affected | 199 | **39** |

Top remaining genuinely-unresolved modules: `versioned` (6),
`persistent_trie`/`persistent_map`/`persistent_list`/`persistent_vec`/
`persistent_set`/`persistent_sorted_map`/`atom`/`combinators` (4 each),
`signature.key_ops`, `file`, `game_engine.effects`, `collection_helpers` (2 each).

**The docs anchor spec is ALREADY FIXED.**
`test/01_unit/lib/math/bignum/bignat_spec.spl` imports
`std.math.bignum.limb` and `std.math.bignum.bignat`; both resolve today to
`src/lib/common/math/bignum/limb.spl` and
`src/lib/common/math/bignum/bignat.spl`. `src/lib/math/bignum/` never existed —
the module lives under the `common/` family. The anchor should be re-pointed at
one of the 39 files that genuinely still fail, e.g. a `persistent_*` spec.
