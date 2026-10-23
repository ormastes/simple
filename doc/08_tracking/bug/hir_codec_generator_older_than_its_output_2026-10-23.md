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

## Correction 2026-10-23: claim 3 above was WRONG, and the repair is now landed

**Claim 3 ("Regenerating drops nil guards on node payload fields") is false.**
`codec_gen.spl:445-448` does emit the guard (`val enc_node_vN: T = v` followed
by a presence check). The 12 `enc_node_vN` lines I read as removals were
RENUMBERED bind counters: the measured diff has 12 removals and 12 additions of
that class, equal counts. I misread a renumbering as a deletion. Claims 1 and 2
stand and were both verified by running the generator.

**Claims 1 and 2 are now repaired**, and the repair is verified:

- the dangling `src/lib/common/facet_abi.spl` declaration source and its emitted
  `use common.facet_abi.*` are removed, so the generator runs;
- the encoder default arm emits `w.reject("unencodable <T> enum")` again instead
  of the process-exiting `hc_bad_tag(..., -1)`, and the emitted header comment
  matches that behaviour.

With both repaired, regeneration produces a **94-line, fully-explained diff**:
13 added lines encoding the four `nogc_*` HirFunction fields the committed
output was missing, the cosmetic `enc_node_vN` renumbering, and **zero**
unexplained removals. All 32 `w.reject("unencodable ...")` arms are preserved.
`HIR_CODEC_VERSION` is bumped to `spl-hircodec-v10-nogc-fields` because the
added fields change the wire format, so stale cache entries must be rejected
rather than mis-decoded.

Verified on the stage-2 sanity battery (Linux x86_64, cranelift): Stage 2 builds
(`Cache: reused 0 modules; rebuilt 1487`), `p2_add` passes, no snapshot drift,
and the only failure is the pre-existing `stage2-module-path-naming-build`
SIGSEGV — identical to the run before this change. So the regeneration does not
regress anything observable; it restores the ability to regenerate at all.

### Next-step 2 above is DISPROVED — do not retry it

That step proposed making a non-optional `i64`/`bool` reject the nil sentinel.
It was implemented (161 emitted reject sites), built into a Stage 2 candidate,
and **the SIGSEGV was unchanged**: same route
(`hir_cache_store` -> `hir_module_decode_stable` -> `hir_module_encode`) and the
same frame `hc_enc_hir_expr_kind`. The nil sentinel is therefore NOT the source
of the corrupt payload, and that change has been dropped rather than landed as
a non-fix. It may still be worth having as hardening, but it needs its own
record and its own evidence.

This makes three disproved hypotheses for
`stage2_sanity_module_path_naming_probe_segv_2026_10_22`: the method-call
argument family (its own next-step 2), `SIMPLE_HIR_CACHE=0` as a workaround, and
the nil sentinel. The remaining question is what else leaves a payload slot
unreadable in a module that `hir_module_decode` accepts.

## Correction 2: the regeneration diff was NOT "fully explained" either

Review of the parity change caught a second false claim of mine, of the same
shape as claim 3: I described the 94-line regeneration diff as "13 `nogc_*`
additions + cosmetic renumbering, zero unexplained removals". There is a **third
wire-format change** in it.

`HirStmtKind.Assign.op` is declared `HirAssignOp?`
(`hir_definitions.spl:801`) — OPTIONAL. The committed output encoded it as a
non-optional node (one presence byte); the regenerated output adds the optional
layer (two presence bytes). Encoder and decoder agree, so this is not
corruption — it is the same shape the generator already emits for other
optional node fields — but it changes the bytes of **every compound
assignment**, and my record did not say so. Anyone diffing v9 against v10 blobs
would have seen Assign bytes move and had no explanation for it.

Also corrected: the four new fields are on **`HirModule`**
(`hir_types.spl:54-57`), not `HirFunction` as I first wrote.

So the regeneration carries three wire-format changes, not one:
1. four `nogc_*` `HirModule` fields the committed output never encoded;
2. `Assign.op`'s optional layer;
3. (cosmetic only) `enc_node_vN` bind renumbering, 12 for 12.

The `HIR_CODEC_VERSION` bump covers all three, which is why a stale v9 entry is
rejected rather than mis-decoded.

## Decode paths: exercised, and 4 pre-existing failures found

The parity verification was initially encode-only — the stage-2 run reported
`Cache: reused 0 modules; rebuilt 1487`, so no v10 blob was ever DECODED. Ran
the codec round-trip specs to close that gap:

| spec | result |
|---|---|
| `hir_codec_nil_scalar_optional_spec` | OK, 4/4 |
| `hir_codec_integer_three_spec` | ERROR, executed=7 passed=5 **failed=2** |
| `hir_codec_optional_node_bare_spec` | ERROR, executed=3 passed=1 **failed=2** |

Those 4 failures are **PRE-EXISTING**: running the same specs against origin's
`spl-hircodec-v9-a5-refusal` codec gives byte-identical counts (5/2 and 1/2), so
the parity change is decode-neutral. They are worth their own record — the codec
has 4 failing round-trip examples on `release/1.0.0` today.

Method note, because the first attempt was wrong: `git stash push` on files that
are already COMMITTED stashes nothing, so an isolation run that way silently
tests the same version twice ("No stash entries found" on the pop is the tell).
The valid isolation is `git checkout <base> -- <files>`, run, then
`git checkout HEAD -- <files>`.

## Why `push-hir-codec-complete` stays advisory

Review recommended promoting the existing `push-hir-codec-complete` row
(`config/check/must_check_gates.sdn:103`) from `push_blocking: false` to
blocking, since with the parity repair it can be green for the first time — and
it is: `PASS — 97 declaration(s) covered, generated codec fresh`.

**Declining, on the repo's own documented precedent.** The gate resolves
`SIMPLE_BIN="${SIMPLE_BIN:-$ROOT/bin/simple}"` and exits 2 when that is absent —
measured here: `scripts/check/check-hir-codec-complete.shs: 35: bin/simple: not
found` / `ERROR — nothing was checked`. `.claude/rules/vcs.md:246-251` records
exactly this reasoning for `push-dual-run-shadow`: it "needs a runnable
`bin/simple` and exits 2 without one, which as a blocking gate would block every
push from a binary-less host". Promoting this row would block every push from
such a host, including the pushes that landed this work.

The real gap is different and is worth fixing: `hir-codec-complete` appears in
**no** `.github/workflows/` file, so unlike other advisory rows it has no CI
lane either. That — not blocking-ness — is what let parity drift silently, and
it needs a workflow change that cannot be verified from here.
