# `codec_gen.spl` is older than its own generated output, so the HIR codec cannot be regenerated

- **Date:** 2026-10-23
- **Status:** OPEN — blocks the principled fix for
  `stage2_sanity_module_path_naming_probe_segv_2026_10_22`, and therefore Stage 2
  admission and any full bootstrap on `release/1.0.0`
- **Files:** `src/app/compiler_schema/codec_gen.spl` (the generator),
  `src/compiler/20.hir/generated/hir_codec.spl` (its output, 8,807 lines)

## Why this matters

`src/compiler/20.hir/generated/hir_codec.spl` carries
`# GENERATED — do not edit; regenerate with: bin/simple run src/app/compiler_schema/main.spl codec`.
The stage-2 sanity SIGSEGV located in
`stage2_sanity_module_path_naming_probe_segv_2026_10_22.md` is a codec defect, so
the sanctioned fix is to change the generator and regenerate. **That path is
currently closed**, in three independent ways, each verified below.

## 1. The generator fails outright: a declaration source that never existed

```
$ bin/simple run src/app/compiler_schema/main.spl codec
error: hir codec generator: declaration source missing: src/lib/common/facet_abi.spl
```

`codec_gen.spl:53` lists `"src/lib/common/facet_abi.spl"` in its declaration
sources and `:88` emits `use common.facet_abi.*` into the output. That file:

- does not exist anywhere in the tree (`find src -name facet_abi.spl` → nothing);
- was **never tracked** in git (`git log --all -- 'src/lib/common/facet_abi.spl'`
  is empty);
- is referenced by nothing else except two architecture docs.

The generated codec contains **zero** `facet_abi` references, so it was produced
before that reference was added. `git log -S'facet_abi.spl' -- <generator>` points
at `e274cd33719 chore: merge all share-history worktree branches into main` —
the commit `.claude/rules/vcs.md` already names as the stale-snapshot-rewind
class that `push-no-stale-snapshot-rewind` exists to catch.

Removing both lines makes the generator run and emit a complete codec
(`generated HirModule codec over 97 declaration(s)`), so the reference is
spurious rather than a genuinely missing module. **But running it then regresses
the codec, for the two reasons below.**

## 2. Regenerating replaces clean refusals with process exits

The committed output has, for every enum encoder's default arm:

```simple
case _: w.reject("unencodable AsmConstraintKind enum")
```

The current generator (`codec_gen.spl:673`) emits:

```simple
case _: hc_bad_tag("AsmConstraintKind", -1)
```

`hc_bad_tag` **exits the process**; `w.reject` refuses the cache entry and lets
the build continue. The committed file's own header documents the soft form
("Encoders reject the cache entry; decoders route an unknown stored tag to
hc_bad_tag, which exits"), and `9625bb7a158 fix(codec,runtime): encoder guards
use a REGISTRY-membership probe ... wild nodes are refused cleanly instead of
faulting` is the change that introduced it. That improvement exists in the
OUTPUT but not in the GENERATOR.

## 3. Regenerating drops nil guards on node payload fields

The committed output guards node-typed payload fields before encoding:

```simple
val enc_node_v6: HirExpr = b_value
if not enc_node_v6.?:
    hc_enc_hir_expr(w, enc_node_v6)
```

Today's generator emits no such guard, so regenerating removes it — 16 removed
lines of this class in a measured diff. These are precisely the guards that
matter for the located SIGSEGV, which faults while encoding a payload slot.

## Measured diff

Generator repaired only enough to run (facet_abi reference removed), then
regenerated and diffed against the committed output: **1,048 diff lines**. Three
classes:

| class | direction | assessment |
|---|---|---|
| `w.reject` → `hc_bad_tag` | regression | a refusal becomes a process exit |
| node-field nil guards dropped | regression | removes protection for the open SIGSEGV |
| `nogc_strict`, `nogc_param_effects_checked`, `nogc_param_effect_symbol_ids`, `nogc_param_effects` added | the output is ALSO stale | committed codec does not encode these HIR fields |

So the generator and its output have drifted in **both** directions: the output
has hand/older-generator improvements the generator lost, and the generator knows
about HIR fields the output lacks.

## What this does NOT claim

- It does not claim regenerating is the cause of the stage-2 SIGSEGV. The
  committed codec is what the failing candidate was built from.
- It does not claim the `nogc_*` field gap is harmful on its own: encode and
  decode in the committed file are consistent with each other, so a blob written
  and read by the same codec round-trips those fields' absence symmetrically.
- It does not identify which lost generator commits are involved beyond
  `9625bb7a158`; the archaeology is not done.

## Next steps

1. Bring `codec_gen.spl` back to parity with its output before any regeneration:
   restore the `w.reject` default arm and the node-field nil guards, and drop the
   dangling `facet_abi.spl` reference. Verify by regenerating and diffing against
   the committed file — the diff should be EMPTY before any new change is added.
2. Only then apply a codec fix. The prepared one for the open SIGSEGV is to make
   a non-optional `i64`/`bool` field **reject** the nil sentinel instead of
   storing `nil` in a typed slot: the decoder currently emits
   `val f_value = if raw0 == "N": nil else: flat_pool_parse_i64(raw0)` and then
   `HirExprKind.IntLit(f_value, f_suffix)`, where
   `IntLit(value: i64, suffix: text?)` (`hir_definitions.spl:567`) is
   non-optional. There are 158 such `if rawN == "N": nil else:` sites. Failing
   closed turns the SIGSEGV into the counted `_hir_cache_refuse("unstable")` the
   store path already expects.
3. Consider a gate that regenerates the codec and fails when the result differs
   from the committed file. The drift above is exactly what such a gate catches,
   and nothing currently does.
