# Bug cluster #169 remainder — enum values in Dict on native --entry path

Worktree: `/tmp/wt_edict` @ f88995e9d81a030fde96dd3310aeb5c8014f9703
Patch: `scratchpad/enum_dict.patch`

## Re-characterization (BEFORE any fix in this session)

Ran the 4 requested probes against the worktree exactly as it stood after Part A
(bare Some/None, tuple destructure, void-alloca fixes). Result: **none of them
hit an llc type error.** They all built and ran (exit 0) but produced **silent-
wrong** output (mostly "no output at all" for the enum/Dict cases). Digging in
found this was not enum- or Dict-specific: even the most trivial

```
val x: i64 = 42
print(x)
```

built clean and printed `0` instead of `42` on this exact worktree tip. So the
real, currently-live bug is upstream of anything Dict/enum-specific: it's a
general var/val-initializer-drop bug in the LLVM alloca-slotting MIR pass,
which the Dict/enum probes happen to trigger because they all declare a local.

| # | Program | Before fix | After fix |
|---|---------|-----------|-----------|
| 1 | `Dict<text,MyEnum>`, payload-less `A`/`B`, `match d["k"]:` inline | builds, exit 0, **no output** (silent-wrong: neither case matched) | builds, exit 0, prints `1` (correct: A) |
| 1b| same, via intermediate `var v: MyEnum = d["k"]; match v:` | same silent-wrong | prints `1` (correct) |
| 2 | `Dict<text,MyEnum>` with `C(41)` payload variant, matched by construction | not reached (1 already broken) | builds, prints `41` (correct, by-construction check) |
| 3 | `Dict<i64, i64?>` with `Some(41)`/`nil` values, matched | N/A (also affected by the general bug: plain `Dict<text,i64>` round-trip printed `0` instead of `5`) | builds, prints `41` then `888` (correct) |
| 4 | `[MyEnum]` array with `A` and `C(41)`, matched by index | same general bug (`val x = 42` broken) would have hit this too | builds, prints `1` then `41` (correct) |
| multi | one `main` combining all of the above (plain match, array, dict-plain-enum, dict-payload-enum, dict-option) in sequence | not applicable | builds (~85s under shared-machine load), prints `214114141888` — matches expected `2,1,41,1,41,41,888` exactly |

Also found: `Dict.len()` always returns `0` on this native path (`rt_len(...)`
declared as a bare variadic extern with no real MIR-level wiring) and
`.has()`/`.contains_key()` aren't lowered at all (`unresolved method call`,
loud MIR error — correctly gated, not silent). Both are **pre-existing, out of
scope for #169** (not enum/Dict-value-boxing issues) and are noted below as
follow-on bugs rather than fixed here.

## Root cause

File: `src/compiler/60.mir_opt/mir_opt/var_reassign_analysis.spl`
Functions: `var_reassign_operand_local` (line 99) and `var_reassign_written_local`
(line 124), both previously declared `-> i64?` (`Option<i64>`).

**The bootstrap-seed interpreter's `.?` presence check on `Option::Some(0)`
evaluates falsy.** It appears to forward the boxed payload itself as the
truthiness value rather than a real Some/None tag, so `Option::Some(0).?`
reads as `0` (falsy) while `Option::Some(1).?` etc. read correctly as truthy.
Confirmed by direct instrumentation of `ssa_local_defined_in_block`:

```
[DEBUG-defblk] local_id=0 FALSE-BRANCH written=Option::Some(0)
[DEBUG-defblk] local_id=0 TRUE-BRANCH written.unwrap()=1
...
```

i.e. `if written.?:` visibly took the **false** branch when `written` was
literally `Option::Some(0)`.

Impact chain, concretely for `val x: i64 = 42; print(x)`:
1. MIR local id `0` is a `Temp` holding the `Const(42)` def; local id `1` is
   the `Var` "x" (`Copy(dest=1, src=0)`), followed by the print call chain.
2. `ssa_cross_block_live_locals` (in `var_reassign_ssa.spl`) calls
   `ssa_local_defined_in_block(block, 0)`, which loops instructions calling
   `var_reassign_written_local` and gates on `.?`. For the `Const` instruction
   (`written = Option::Some(0)`), the gate is **falsy**, so the def is
   invisible to this analysis — local `0` is misreported as "used but never
   defined in this block" → flagged cross-block-live even though it's a
   single-block function.
3. This wrongly adds local `0` to the `slotted` set in
   `ssa_alloca_transform_blocks` (`_MirToLlvm/core_codegen.spl` calls into
   `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl`), which allocates a
   stack slot for it (`alloca`) and rewrites its *reads* to `Load` (index-based
   lookup, unaffected by the Option bug).
4. But the matching *write* rewrite, `ssa_alloca_apply_def_store` (line
   ~1287 of `var_reassign_ssa.spl`), *also* gates on `written.?` — so for the
   very `Const(dest=0, 42)` instruction that supposedly justified slotting
   local 0 in the first place, the `Store` into the alloca is **also
   skipped**. Net result: `alloca` + `load` with **zero stores** — the load
   reads uninitialized stack memory (observed as 0 in this environment).

IR evidence (`SIMPLE_KEEP_LLVM_IR=1`, before fix), the smoking gun:
```llvm
bb0:
  %l5 = alloca i64, align 8
  %l0 = add i64 42, 0  ; const int      <- computes 42, but never stored to %l5
  %l6 = load i64, ptr %l5, align 8      <- reads uninitialized slot
  %l1 = add i64 %l6, 0  ; copy
  ...
  call void @rt_print(ptr ...)          <- prints 0
```

For the Dict/enum tests specifically, the same mechanism made the Dict-value
local (holding the boxed enum handle) silently uninitialized after
store/retrieve round-trips through `Dict<text, MyEnum>`, which is why `match`
never hit either arm (comparing an uninitialized/garbage discriminant against
0/1).

This is the same class of bug flagged in project memory as the "Option<i64>
tag-box boxing landmine" (`char.to_i64`/`Option<i64>` collision with 0) — a
known footgun of this interpreter, not a bug in the compiled program's actual
LLVM lowering logic itself.

## Fix

Changed `var_reassign_operand_local` and `var_reassign_written_local` from
`i64?` (`Option<i64>`) to plain `i64`, using `-1` as the "no local"/"not
applicable" sentinel (local ids are always `>= 0`, so `-1` is collision-free).
Updated every call site across both files (`var_reassign_analysis.spl`,
`var_reassign_ssa.spl`) from `.?`/`.unwrap()` to `!= -1`. This includes the
already-slotting fast path (`ssa_alloca_apply_def_store`, which had a comment
documenting a *related* but different landmine — a negated-`.?` bug — already
worked around there; this fix removes the Option type entirely so neither
variant of the landmine can recur) plus `ssa_local_defined_in_block`,
`ssa_reassigned_locals_for_blocks`, `ssa_block_written_locals`,
`ssa_operand_push_local`, `ssa_max_local_from_operand`,
`ssa_max_local_from_inst`, and the two callers in
`var_reassign_analysis.spl` (`var_reassign_update_aliases_for_inst`,
`analyze_var_reassign_blocks`).

Left untouched (out of scope, no repro forced it): `ssa_phi_plan_pred_value_for_block`
(line 815 of `var_reassign_ssa.spl`), the older phi-based SSA fallback path
that only runs when the alloca transform reports "not applied" — every repro
in this task went through the (now-fixed) alloca transform. Flagged as a
follow-on risk since it returns `i64?` too and could hit the same landmine on
some other input shape.

No loud→silent-wrong conversions: `.unwrap()` and `.has()`/`.contains_key()` on
Dict remain properly loud MIR-lowering errors (verified exit != 0, no binary
emitted) — those are pre-existing unrelated gaps, not touched.

## Verification battery (after fix)

All via `env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry <p>.spl -o out --clean && ./out`
from the worktree root, `bin/simple` symlinked to the shared release binary.

| Program | Build | Run output | Expected | Pass |
|---|---|---|---|---|
| `val x: i64 = 42; print(x)` | exit 0 | `42` | `42` | yes |
| `var x: i64 = 42; print(x)` | exit 0 | `42` | `42` | yes |
| plain enum match (`MyEnum.A`, no Dict) | exit 0 | `1` | `1` | yes |
| `Dict<text,i64>`, same-literal key, store 5 / read / print | exit 0 | `5` | `5` | yes |
| `Dict<text,MyEnum>` payload-less, inline `match d["k"]:` | exit 0 | `1` | `1` | yes |
| `Dict<text,MyEnum>` payload-less, via `var v` then `match v:` | exit 0 | `1` | `1` | yes |
| `Dict<text,MyEnum>` with `C(41)` payload, matched | exit 0 | `41` | `41` (by construction) | yes |
| `Dict<i64,i64?>` `Some(41)`/`nil`, matched | exit 0 | `41888` (no newline) | `41`,`888` | yes |
| `[MyEnum]` array with `A`, `C(41)`, matched by index | exit 0 | `141` (no newline) | `1`,`41` | yes |
| multi-construct: plain + array + dict-plain + dict-payload + dict-option, one `main` | exit 0 (~85s, shared-machine load) | `214114141888` | `2,1,41,1,41,41,888` | yes |
| `Dict<text,i64>.has("k")` | loud MIR error (`unresolved method call: has`), no binary | n/a | still loud (pre-existing gap, untouched) | correct behavior preserved |
| `.unwrap()` on `i64?` | loud MIR error (`unresolved method call: unwrap`), no binary | n/a | still loud (pre-existing gap, untouched) | correct behavior preserved |
| `Dict<text,i64>.len()` | exit 0, prints `0` | n/a | pre-existing separate bug (`rt_len` stub), not part of #169, left as-is | noted, not fixed |

## Smoke matrix

`sh scripts/check/native-smoke-matrix.shs` (run from /tmp/wt_edict with the fix
applied): **total=15 pass=14 fail=1 xfail=0 xpass=0 codegen_fallback_hits=0**.
Sole failure = `option_nil_check` (rc got=1 want=7), the one allowed failure
per the gate. All enum/dict-relevant rows green: `enum_construct` (7),
`enum_match` (8), `dict_index` (13), `result_try_op` (15). Gate (>=14/15,
0 fallback hits, only option_nil_check allowed): **MET**.

Note: `option_nil_check` exercises `x.?` — the native-side sibling of the same
`.?`-on-Some(payload) truthiness landmine documented as root cause above. It
fails identically on the green base; this patch neither fixes nor regresses it.

## Files changed

- `src/compiler/60.mir_opt/mir_opt/var_reassign_analysis.spl`
- `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl`

Patch: `scratchpad/enum_dict.patch`. Worktree not committed/pushed, left for
caller to review; `git worktree remove --force /tmp/wt_edict` still pending
until final review confirms.
