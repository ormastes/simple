# Bug: interpreter binds the first param of *some* multi-param `me` methods to value×8

**Filed:** 2026-06-29
Status: FIXED 2026-08-17 (P1) — root-caused, patched, and verified by EXECUTION.
See the '2026-08-17 ROOT CAUSE + FIX' section at the bottom.
**Affects:** `bin/simple run` = the **JIT/native lane**, NOT the tree-walk interpreter. The
`interp_` prefix in this filename and the word "interpreter" throughout the original text are
a **misnomer** — kept only so links don't rot. **Conditional** — does not reproduce in isolation.
**Family:** the `<<3` tag-box family (missing unbox), *not* a receiver-slot/arg-offset error.

## Symptom
For certain multi-parameter `me` methods, the FIRST positional parameter binds to
`value × 8` (= `sizeof(i64)`) on method entry. The remaining parameters are correct.
Capturing the first param into a local on the first line does not help — it is already
`×8` when read, so the corruption is at parameter binding, not use.

Confirmed live in exactly one place so far: `examples/09_embedded/simpleos_nvme_fw/fw/ftl_journal.spl`,
method `append(map_lba, old_ppn, new_ppn, map_seq)`. With the natural 4-param signature,
`append(100, 10, 20, 1)` stores `wal_lba = 800`; the self-test catches it
(`record_lba(0)` expected 100, got 800).

## NOT universal — and not reproducible in isolation
Most multi-param `me` methods are unaffected (verified by round-trip self-tests):
`fil_nand.program(ppn,lba,seq,data)`, `fw_pool.acquire(cid,lba,nblk,data)`,
`fw_pool.set_ppns(h,old,new,seq)` all round-trip every param correctly. Minimal repros that
mirror `append`'s shape do **not** reproduce the ×8:
- `me poke(idx, v)` with `me.a[idx]=v` → correct (first param as index).
- `me store4(v1,v2,v3,v4)` / `store5(...)` with `me.arr[me.cnt]=v1` → correct (first as value).
- `me s_local` (local before use), `me s_guard` (if-guard before use) → correct.
- An exact replica of `append` (struct with 4 `[i64]` fields of length 512 + cap/cnt scalars,
  same guard + `val slot` + four `me.aN[slot]=pN` stores) → **correct**.

So the trigger depends on something beyond method shape — likely the interpreter's
method-table / call-frame slot layout for the specific `impl` (e.g. the particular set and
order of methods in `Journal`). Single-parameter `me` methods are always unaffected.

## Repro (in context)
1. In `ftl_journal.spl`, change `me append(_p0, map_lba, old_ppn, new_ppn, map_seq)` to drop
   `_p0` and update the 3 self-test call sites to 4 args.
2. `bin/simple run` a harness calling `ftl_journal_selftest()` → 3 FAILs, each an lba `×8`.

## Workaround (applied)
Add a leading dummy `_p0: i64` param (callers pass `0`). The corrupted "first param" is then
a throwaway and the real args start at position 2. See `fw/CONVENTIONS.md`. The clean form
for new code is a single struct param (single-param `me` methods never trip the bug).

## Detection rule
Every multi-param `me` method's self-test must round-trip EACH stored parameter value, so a
`×8` corruption surfaces as a failed assertion rather than silent data corruption.

## Root-cause hypothesis (ORIGINAL, 2026-06-29 — now SUPERSEDED, see below)
Off-by-`sizeof(i64)` in the interpreter's argument-slot addressing for `me` methods, gated by
a layout condition (method count/order in the `impl`, or field count) that shifts the first
arg's computed offset. Needs a seed-interpreter investigation + a reduced trigger.

---

# Triage 2026-08-01 — static analysis only (no builds; ENOSPC)

Read-only source triage. **Nothing was re-run**: the filesystem was in a btrfs metadata-ENOSPC
state, and the live `bin/simple` has lost its `run`/`test` subcommands, so no repro was
attempted. Every claim below is source-derived; the untested parts are marked.

## 1. It is a VALUE-ENCODING error, not a receiver-slot / arg-offset error — DECIDED

The `×8` is exactly the tag-box shift. In the Rust seed runtime:

- `src/compiler_rust/runtime/src/value/tags.rs:4` — `pub const TAG_INT: u64 = 0b000;`
- `src/compiler_rust/runtime/src/value/core.rs:200-203` — `from_int(i) -> Self((i as u64) << 3)`
- `src/compiler_rust/runtime/src/value/core.rs:214-217` — `as_int() -> (self.0 as i64) >> 3`

Because `TAG_INT` is **zero**, a boxed integer whose `as_int()` unbox is skipped reads as
*exactly* `value * 8`. There is no other `×8` in the value representation.

**Why this rules out the receiver-slot hypothesis.** The original hypothesis (off-by-one on
`me`'s implicit receiver slot, i.e. the first param reading a neighbouring slot) predicts the
first param receives a *different operand* — the receiver pointer, or another argument. Such a
value does **not** track the input. The recorded observations do: `100 → 800`, `101 → 808`,
`102 → 816`, three distinct inputs each scaled by exactly 8 and by nothing else. A slot
misalignment cannot produce a value that is a linear function of the correct value. The
corruption is the *right operand in the wrong encoding*. The two failure modes are
externally identical and demand different fixes, and this one is the encoding fix.

## 2. Which engine — the original attribution is unsupported

`bin/simple run` is the **JIT/native** lane; `bin/simple test` is the tree-walk interpreter.
They are different engines, so "interpreter" cannot be inferred from a `run` repro. Worse, the
2026-06-29 investigation predates the discovery that the engine knob of the era did not work:
`doc/08_tracking/bug/list_get_returns_tag_boxed_value_shifted_left_3_2026-07-28.md` records
that `SIMPLE_NO_JIT=1`, `--interpret`, `--no-jit` and `bin/simple-interp` were all **no-ops on
the seed** (only `SIMPLE_EXECUTION_MODE=interpret` selects the interpreter; unrecognized values
fail open to JIT at `exec_core.rs:41`). Any "reproduced under the interpreter" claim from
before `b7151d94114` proved nothing.

The same doc's truth table for the family is decisive on direction: JIT/native returns the
`<<3` word (wrong), the tree-walk interpreter returns the correct value. **Lane: seed
JIT/native.** Pure-Simple lane: untested, and unrelated to this repro.

## 3. Same root as the `<<3` family — with one caveat

Same primitive, same signature, same lane as:
- `list.get(i)` returning `value << 3` while `xs[i]` is correct (42 → 336, 7 → 56 — the case
  once misfiled as Dict corruption). Root cause there: *the boxed slot word returned without
  applying the unbox shift that the index-read path applies.* Identical description fits here.
- var born `[]` then rebound reading shifted-by-3 under native codegen.
- `??` on a raw i64 corrupting index 3 / the JIT Option-i64 value-3 collision — those are the
  *tag-space* half of the same representation (the nil sentinel **is** 3).

Caveat, and it is why this is "same family, distinct site": in `list.get` the missing unbox is
on a **return** value; here it is on an **argument** at a call boundary. Same defect class
(a `RuntimeValue` crossing a boundary without `as_int()`), different crossing.

**Probe-artifact check — passed.** The `list.get` investigation was once derailed by a probe
that read results back through the broken `.get()`. This bug is *not* that: `record_lba` reads
via the bracket path `me.wal_lba[ridx]` (`ftl_journal.spl:137`), which is the *correct* path,
and the sibling fields `wal_old`/`wal_new`/`wal_seq` read back correctly through the identical
idiom in the same self-test. The measurement is sound.

## 4. What the "conditional" actually is — narrowed, not closed

The original doc's counterexamples are strong negative evidence and they **eliminate** the
conditions people usually reach for first:

| candidate condition | verdict | killed by |
|---|---|---|
| param arity (4 args) | ruled out | `fil_nand.program`, `fw_pool.acquire`, `fw_pool.set_ppns`, `store4`, `store5` all correct at the same arity |
| "first param is a value not an index" | ruled out | `store4`/`store5` correct with first-as-value |
| struct shape / 4 `[i64]` fields of 512 | ruled out | the exact replica is correct |
| method count/order in the `impl` | unsupported | never tested; no mechanism in the source connects method-table order to argument encoding |

**Param-index vs field-index — the workaround discriminates.** `map_lba` was simultaneously
param #0 and stored into field #0 (`wal_lba`), so the two were confounded. Adding the dummy
`_p0` shifted the **param** index to 1 while leaving the **field** index at 0 — and the
corruption disappeared. So the trigger tracks the parameter position, not the field position.
That is the one solid inference the original investigation produced, and it survives.

**What `append` has that every non-reproducing replica lacks.** `append` executes a chain of
nested `me`-method calls *before* the first parameter is ever read:

- `ftl_journal.spl:95` — `val count = me.effective_count()`
- → `:80` — `me.physical_cap()`
- → `:58-65` — four `.len()` calls on the `[i64]` fields
- `ftl_journal.spl:101` — `if not me.wal_slot_ready(count)` → `:69` → `me.physical_cap()` again

Only at `:104` is `map_lba` first read. No replica listed in the original doc has a nested
`me`-call chain ahead of the parameter use; they guard with plain comparisons. **The proposed
condition is therefore: the first parameter's boxed argument slot is live across a nested
`me`-method call and is restored/re-read in the boxed encoding.** This is corroborated by the
sibling defect in the same firmware,
`doc/08_tracking/bug/interp_method_call_result_as_arg_corruption_nested_2026-06-30.md`, which
documents value corruption at exactly the `me`-call boundary and is likewise context-dependent.

**Status of this hypothesis: UNVERIFIED.** It is the only surviving structural difference, but
it was not reduced to a repro (no builds permitted this session). The falsifying experiment is
cheap and is listed below.

**Ruled out as the mechanism:** `native_worker_arg` / `raw_worker_args`
(`src/compiler_rust/runtime/src/executor.rs:633-635`, flag computed at `:653` from the
pointer-range heuristic `closure_arg > X86_64_MAX_CANONICAL_USER_PTR`). This *is* a real
boxed-vs-raw argument convention chosen conditionally, and it is the archetype of this bug
class — but it serves only the single-argument closure/worker dispatch path, which
`j.append(...)` does not reach. Worth naming so the next investigator doesn't re-find it and
mistake it for the answer.

## 5. Reachability at HEAD

The defect has never been fixed, only masked: the `_p0` workaround is still in the source
(`ftl_journal.spl:94`, call sites `:191-193`, `:211`), and the encode/decode primitive at
`value/core.rs:200-217` is unchanged. Nothing in the seed has been altered to unbox arguments
at a `me`-call boundary. **The mechanism can still occur at HEAD** — subject to the caveat that
the trigger condition itself is still unproven.

## 6. Recommended change — NOT MADE

1. **Do not touch `ftl_journal.spl`.** Keep `_p0` until the compiler fix lands; removing the
   workaround without a fix silently re-corrupts WAL LBAs.
2. **Reduce the trigger first (one experiment, decides everything).** Take the replica that
   already passes and add a nested `me`-method call before the first param is read. If it goes
   `×8`, the condition is confirmed and the search collapses to the argument lowering around
   nested calls. Run it on both engines via `SIMPLE_EXECUTION_MODE=interpret` — never
   `SIMPLE_NO_JIT=1`, which is a no-op on the seed.
3. **Fix belongs in the JIT argument lowering, not in call sites.** Ensure every i64 parameter
   slot is unboxed with `as_int()` on method entry, and audit argument-slot save/restore across
   a nested `me` call. As with `list.get`, this is one lowering fix, not a sweep.
4. **Correct the record.** Retitle away from `interp_` (JIT/native lane) and fold this into the
   `<<3` tag-box family index so it is not investigated a third time as a slot-offset bug.
5. **Generalize the detection rule.** The existing rule (round-trip every stored param) is good
   but reactive. The class-level check is: assert on any readback that equals `expected * 8`
   and report it as a tag-box escape, not as data corruption — the `42 → 336` precedent cost a
   month aimed at the wrong subsystem.

## Unfinished
- The nested-`me`-call condition is **hypothesis, not fact** — no repro was run.
- The exact JIT argument-lowering site was not pinned to a file:line; a delegated search of the
  seed's method-call argument path did not return before this session was interrupted.
- Pure-Simple lane behaviour is untested.


## 2026-08-17 CORE-P1 triage: DID NOT REPRODUCE / fix present in current source

Verified against CURRENT SOURCE (content, not SHA ancestry) during the crit_01
CORE-P1 sweep. The x8 symptom is `<< 3`, the int-boxing shift -- this was one face of the unguarded 61-bit box, not a distinct parameter-binding defect. `src/compiler_rust/runtime/src/value/tags.rs` is now 14 lines of pure constants (`TAG_MASK 0b111`, `TAG_INT/HEAP/FLOAT/SPECIAL`) with no shift/boxing logic, so no double-shift is reachable from it; the shift now lives in `runtime/src/value/core.rs` `from_int` and is range-guarded. The `_p0` dummy-first-param workaround is GONE: `/usr/bin/grep -rn "_p0"` over `compiler/src` and `runtime/src` returns zero hits. COLLAPSES into the same root cause as jit_i64_boundary_constant_wraps_to_negative_2026-08-09.


---

# 2026-08-17 — ROOT CAUSE + FIX (verified by EXECUTION, CRITICAL lane)

## Reproduced first

Binary `bin/release/x86_64-unknown-linux-gnu/simple` (59,536,728 bytes, mtime
2026-08-16 22:59, Rust seed). A copy of `examples/09_embedded/simpleos_nvme_fw/fw`
was taken under scratch, the `_p0` workaround removed from `me append`, and the
7 call sites updated. `ftl_journal_selftest()`:

```
=== default:            FAIL record_lba(0) -- expected 100 got 800
                        FAIL record_lba(2) -- expected 102 got 816
                        FAIL recovered WAL append stores lba -- expected 199 got 1592
                        FAIL surviving record lba -- expected 102 got 816
                        FAILS=4
=== SIMPLE_EXECUTION_MODE=interpreter:  FAILS=0
=== SIMPLE_EXECUTION_MODE=jit:          FAILS=4   (identical to default)
```

Confirms the doc's later note: this is the **JIT lane**, not the tree-walk
interpreter. A `print` as the first statement of `append` showed
`ENTRY map_lba=800 old=10`, so the corruption is at parameter binding, before
any use.

## The doc's framing was wrong on two counts

Reduced to a 10-line single-file repro (the doc claimed minimal repros do not
reproduce — they do, once you keep the *method name*):

```
struct J:
    c: i64

impl J:
    me append(p1: i64, p2: i64) -> i64:
        print("E " + p1.to_text())
        me.c

fn main():
    var j: J = J(c: 0)
    j.append(100, 10)        # prints "E 800"
```

- Renaming `append` -> `appendZZ` makes it correct. Renaming the *parameter*
  does not. `me push(...)` reproduces identically; `me insert(...)`/`me zzz(...)`
  do not.
- **Single-parameter `me` methods ARE affected** — `me append(p1: i64)` prints
  `800`. The doc's "single-param `me` methods never trip the bug" claim is false;
  it only looked true because no single-param method in that tree was named
  `append`/`push`.
- A `text` first parameter is unaffected — it is integer boxing specifically.
- A free function `fn append(p1, p2)` is unaffected — receiver-method path only.

So this is **not** a call-frame/arg-slot layout defect and **not** conditional on
method count or `impl` order. It is a **method-name collision** with the builtin
array mutators.

## Root cause

`src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs`

```rust
let is_array_append_method = method == "push" || method == "append";   // :1541 — NAME ONLY
...
if is_array_append_method && !args.is_empty() {                        // :1606 — NO receiver gate
    // BoxInt (v << 3) the first integer argument so rt_array_push sees a tagged element
```

The boxing block exists so genuine `arr.push(x)` stores a tag-boxed element
matching `IndexGet`'s `UnboxInt`. But its guard is the method NAME alone. With a
struct receiver the call still dispatches to the user's own method
(`SIMPLE_DEBUG_METHOD_DISPATCH=1` confirms `func_name='J.append' args=2`), which
reads the parameter raw — so it arrives as `v << 3`, i.e. `value * 8`. The `* 8`
in the title is exactly the boxed-int tag shift, as the 2026-08-01 triage
suspected.

The sibling `index_of` boxing block **20 lines below in the same function** was
already correctly gated on `self.receiver_is_array(receiver, receiver_local_ty)`.
The append/push block simply never got that gate.

## Fix

Added the same gate at `lowering_expr_method.rs:1606`:

```rust
if is_array_append_method && !args.is_empty() && self.receiver_is_array(receiver, receiver_local_ty) {
```

## Verified by EXECUTION after the fix

Rebuilt seed at `/mnt/data/cargo-target-c1b-a/release/simple` (`cargo build
--release --bin simple`, exit 0, 16m19s).

| probe | before | after |
|---|---|---|
| `ftl_journal_selftest()` with `_p0` removed, JIT | `FAILS=4` | `FAILS=0` |
| `probe_user_method_builtin_name_append_jit.spl`, JIT | `5 FAILURES` | `ALL PASS` |
| `probe_builtin_name_collision_arg_transport_jit.spl`, JIT | `3 FAILURES` | `ALL PASS` (1 known-open, see below) |
| `probe_scalar_slot_roundtrip_jit.spl` (regression control), JIT | `ALL PASS` | `ALL PASS` |

Genuine `arr.push(7)` / `arr.append(9)` / `[f64].push(2.5)` / `arr.index_of()`
still round-trip — the gate does not disable real array element boxing.

## Specs

- Reproducing: `test/01_unit/compiler/codegen/user_method_named_append_arg_boxing_spec.spl`
  (+ probe `probe_user_method_builtin_name_append_jit.spl`)
- Class detection: `test/01_unit/compiler/codegen/builtin_name_collision_arg_transport_spec.spl`
  (+ probe `probe_builtin_name_collision_arg_transport_jit.spl`) — defines a user
  method for every builtin name the lowering/codegen tables special-case and
  round-trips an int and an f64 through each.

## Found by the class-detection probe: a separate, still-open sibling

`c.char_code_at(42)` on a struct receiver returns **0** — the call is stolen
outright, not merely rewritten. Different root cause (codegen qualified-name
suffix resolution), filed as
`doc/08_tracking/bug/codegen_user_method_stolen_by_builtin_name_suffix_2026-08-17.md`.
It is reported on its own verdict line in the probe so it can neither be dropped
nor mask a new regression.

## Follow-up NOT done here (outside this lane's file slice)

`examples/09_embedded/simpleos_nvme_fw/fw/ftl_journal.spl` still carries the
`_p0: i64` dummy-parameter workaround and the `NOTE(interp bug)` comment at
:90-94, plus the note in `fw/CONVENTIONS.md`. Both can now be removed — verified
by executing the de-workaround-ed copy above — but the file is owned by another
lane in this wave.
