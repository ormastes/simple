# `var q: T = p` does NOT copy a struct's nested array — it aliases (Rust seed)

**Date:** 2026-09-01 · **Status:** OPEN · **Found by:** D4 per-codeword ECC work
(`examples/09_embedded/simpleos_nvme_fw/fw/`)

## Symptom

Simple's documented value semantics say assignment copies (copy-on-write).
For a struct holding an array field, the Rust seed does not: a write through
the *copy* is visible through the *original*, and through every other binding
that was ever assigned from it.

## Reproducer (6 lines, runs on `bin/simple`, the Rust seed)

```
use nvme_payload.*
fn mutate(p: PageData) -> PageData:
    var q: PageData = p
    q.words[3] = 999
    q
fn main() -> ():
    var a = page_zero()
    a.words[3] = 7
    val b = mutate(a)
    print "a.words[3]={a.words[3]} b.words[3]={b.words[3]}"
    var c = a
    c.words[4] = 55
    print "local alias: a[4]={a.words[4]} c[4]={c.words[4]}"
    return ()
```

Observed:

```
a.words[3]=999 b.words[3]=999
local alias: a[4]=55 c[4]=55
```

Expected (value semantics): `a.words[3]=7 b.words[3]=999`, and `a[4]=0 c[4]=55`.

Both the cross-function form (pass by value, mutate the parameter's copy) and
the purely local form (`var c = a`) alias. `PageData` is
`struct PageData: words: [i64]` — a plain struct with one array field.

## Why it matters

It is silent. Nothing traps; the program keeps running and produces
plausible-looking output. During the D4 ECC work it corrupted two test files
in ways that made them **weaker, not louder**:

* a `flip(p, w, b)` helper meant to return a corrupted *copy* corrupted the
  pristine reference page as well, so a later `page_eq(decoded, base)` compared
  a corrupted page against itself and passed;
* `fil.program_page(ppn, lba, seq, src)` aliased `src` into the media, so a
  subsequent `corrupt_page_word` on the media silently edited the test's own
  expected value.

Both defects made assertions *pass* that should have failed. That is the worst
failure mode for this class of bug.

It also means several pre-existing comments in the fw tree are built on a false
premise — e.g. `fil.spl`'s "Rebuilding through a `var` local keeps the
single-owner rule" on the old `var pg: PageData = res.page; pg.words[0] = ...`.
That code happened to be harmless (its source was a temporary), but the stated
reasoning does not hold on this binary.

## Sites hardened as a workaround

Explicit array-rebuilding copies (`ecc_page_clone`) were introduced rather than
relying on assignment:

* `fw/fil_ecc.spl` — `ecc_page_clone`, and `ecc_page_decode`'s correction path
* `fw/fil.spl` — `Fil.decode_read` legacy repair branch
* `fw/ecc_check.spl` — programs a clone, not the caller's page
* `fw/ecc_codeword_check.spl` — `flip()` deep-copies before flipping

Each site carries a comment saying why, so the workaround is not "simplified"
away by a later cleanup.

## Not investigated

Whether this is specific to `[i64]` inside a struct, to the interpreter vs. the
Cranelift JIT path, or general to all nested collections. No pure-Simple
binary was available to cross-check (`bin/simple` is the Rust seed and says so).

---

## Independent reproduction (parent session, 2026-09-01)

Minimal case, no NVMe code involved:

```simple
struct Box:
    xs: [i64]

fn main():
    val p: Box = Box(xs: [1, 2, 3])
    var q: Box = p
    q.xs[0] = 99
    print("p.xs[0]=" + p.xs[0].to_text())
    print("q.xs[0]=" + q.xs[0].to_text())
    return ()
```

Output:

```
p.xs[0]=99
q.xs[0]=99
```

**Writing through `q` mutated `p`.** `p` is a `val`. The nested `[i64]` is shared
by reference across a struct assignment; no copy-on-write occurs.

## Why this is more serious than the documented COW hazard

`.claude/rules/code-style.md` warns that Simple's value semantics are
copy-on-write and that aliasing a collection causes an O(n) deep copy per write
— a **performance** hazard. This defect is the opposite and worse: for a nested
array inside a struct, the copy does **not** happen, so the aliasing is a
**correctness** hazard. Code written to obey the documented model — "take a
copy, mutate the copy, leave the original alone" — is silently wrong.

Consequences observed in this session:
- It corrupted two of the ECC agent's own test files **in the direction of
  passing**, which is the worst possible direction: a test that should have
  failed did not.
- `fw/fil.spl` carries pre-existing "single-owner" comments whose safety
  argument rests on this false premise. Those are not merely stale comments;
  they assert a guarantee the runtime does not provide.

## Scope — NOT established, must be measured before relying on any bound

This reproduction covers a nested `[i64]` in a struct under `var x = y`. It is
**unknown** whether the same aliasing occurs for: nested `Dict`, nested struct
values, arrays of structs, function-argument passing, and returned values. Do
not assume the defect is narrower than measured — enumerate and test each.

Related defects found the same day, all sharing the signature "silently wrong
value instead of an error":
[[interp_module_val_struct_zeroed_as_call_arg_2026-09-01]],
[[function_argument_types_unchecked_2026-09-01]],
[[simple_run_exit_code_garbage_for_unit_main_2026-09-01]].

## Caveat

Measured on the Rust bootstrap seed (`bin/simple` prints the non-production
warning). A self-hosted retest is blocked by the bootstrap redeploy. Do not
close on a seed-only fix.

---

## Scoping investigation (2026-09-01, follow-up session)

### The single most important correction: this is a **JIT** defect, not a general one

`bin/simple run` does **not** default to the AST interpreter. `ExecutionMode`
defaults to `Jit` when `SIMPLE_EXECUTION_MODE` is unset —
`src/compiler_rust/driver/src/exec_core.rs:223-232` (`Err(_) =>
ExecutionMode::Jit`); only a hardcoded app allow-list forces interpret
(`driver/src/main.rs:1459-1462, 1510-1518`). Every observation in the original
record above was therefore made on the **Cranelift JIT lane**, not the
interpreter. The interpreter is COW-correct on almost every case.

### Probe

`test/fixtures/value_semantics_cow_probe.spl` — 21 cases, each printing
`CASE <n> <name>: PASS|ALIASED`. Run per lane:

```
SIMPLE_EXECUTION_MODE=jit         bin/simple run test/fixtures/value_semantics_cow_probe.spl
SIMPLE_EXECUTION_MODE=interpreter bin/simple run test/fixtures/value_semantics_cow_probe.spl
```

### Measured table (2026-09-01, Rust seed `bin/simple`)

| # | case | JIT | interpreter |
|---|------|-----|-------------|
| 01 | toplevel array, local `var b = a` | PASS | PASS |
| 02 | struct nested `[i64]` | **ALIASED** | PASS |
| 03 | struct nested `Dict` | **ALIASED** | PASS |
| 04 | struct nested struct, scalar field | PASS | PASS |
| 05 | array of structs `[Box]` | **ALIASED** | PASS |
| 06 | struct as fn arg, then local copy in callee | **ALIASED** | PASS |
| 06b | struct fn param, direct write to param | **ALIASED** | **ALIASED** |
| 07 | struct returned from fn | **ALIASED** | PASS |
| 08 | struct constructed from another struct's field | **ALIASED** | PASS |
| 08b | struct field copied to a local array | PASS | PASS |
| 09 | class instance nested array | **ALIASED** | PASS |
| 10 | two-level struct nesting w/ array | **ALIASED** | PASS |
| 11 | struct scalar field | PASS | PASS |
| 12 | `[[i64]]` array-of-array, **no struct** | **ALIASED** | PASS |
| 13 | top-level `Dict`, local `var b = a` | **ALIASED** | PASS |
| 14 | struct nested array `.push()` | **ALIASED** | PASS |
| 15 | `Dict<text,[i64]>` element write, **no struct** | **ALIASED** | PASS |
| 16 | top-level array `.push()` | PASS | PASS |
| 17 | top-level array passed as fn **arg**, written in callee | **ALIASED** | **ALIASED** |
| 18 | top-level `Dict` insert new key through copy | **ALIASED** | PASS |
| 19 | `a -> b -> c` array chain | PASS | PASS |

JIT: 14 of 21 ALIASED. Interpreter: 2 of 21.

**The bug is materially WIDER than "structs".** Cases 12, 13, 15 and 18 involve
no struct at all — a plain top-level `Dict` aliases across `var b = a` on the
JIT, and `[[i64]]` aliases at the inner level. The original record's framing
("nested array inside a struct") under-states it.

**Cases 06b and 17 alias on BOTH lanes** — a direct write to a function
*parameter* is visible in the caller. This is a distinct question (it may be
intended by-reference parameter semantics) and is cross-lane consistent, so it
is NOT part of this JIT defect. It needs its own decision; see
[[function_argument_types_unchecked_2026-09-01]] for the neighbouring class.

**Native/LLVM lane: UNTESTED.** `bin/simple native-build` could not compile the
probe — it fails first with `missing importing module surface` for any path
outside the repo tree, and from inside the tree with
`semantic: panic: compile error: unsupported LLVM value conversion from i64 to
void`. Both are unrelated native-build defects. Do not assume the native lane
matches either measured lane.

### Mechanism (file:line)

The JIT copies a struct with `MirInst::AggregateCopy`, emitted by
`copy_if_value_type` (`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:922-956`).
Its contract is stated at `src/compiler_rust/compiler/src/mir/inst_enum.rs:56-62`:

> Copies `byte_size` bytes of the aggregate's own storage, then deep-copies
> exactly the field slots listed in `deep_fields` — the fields lowering
> positively established to hold a nested DECLARED VALUE TYPE (`struct`).
> **Class/actor/array/text/unknown fields stay shallow**, preserving identity
> semantics and array/text's own already-correct copy paths.

`deep_fields` is built by `struct_deep_fields` (`lowering_core.rs:940-943`) and
consumed by `codegen/instr/closures_structs.rs:509-530` (Cranelift) and
`codegen/llvm/functions.rs:886-888` (LLVM). An `[i64]` field slot is copied
**shallow** — the pointer — so `p.xs` and `q.xs` are the same buffer. The
comment's premise, that "array/text's own already-correct copy paths" will
cover it, is false: those paths run on the *interpreter*, and the struct-block
memcpy on the JIT bypasses them entirely.

The interpreter by contrast is COW-correct by construction: `Arc::make_mut` at
every lvalue hop (`compiler/src/interpreter/place.rs:141-160`), with a
double-gated in-place fast path requiring both `Arc::strong_count(array)==1`
and `Arc::get_mut(fields)` (`interpreter/node_exec.rs:1402-1442`), falling back
to the clone path at `node_exec.rs:1583-1600`.

### This is a KNOWN, previously-triaged defect

- [[jit_struct_assignment_aliases_not_copies_2026-08-10]] — same defect, marked
  "MOSTLY RESOLVED"; the shallow-array-field behaviour is its explicitly
  documented **residual**, deliberately scoped out.
- [[cross_engine_value_semantics_harness_known_red_2026-08-10]] — p1 "JIT
  aliases, interp copies", p2 "shallow AggregateCopy residual; RED even on a
  fresh post-F1 seed".

So the 2026-09-01 ECC-work discovery is a rediscovery, and the cross-engine
harness has been RED on exactly this for three weeks.

### Fix assessment — NOT contained, deliberately NOT attempted

Making `deep_fields` also recurse into array/dict/text field slots is not a
local edit and is not obviously correct:

1. It is not a bug-by-omission but a **stated design choice** (`inst_enum.rs:56-62`)
   made to preserve identity semantics for class/actor fields. Reversing it
   requires deciding, per type kind, which slots are value-typed — and class
   fields must stay shallow, so it cannot be a blanket deep copy.
2. Cases 12/13/15/18 are **not reachable through `AggregateCopy` at all** (no
   struct is involved). They need a separate copy path for top-level `Dict`
   assignment and for nested array elements — that is `copy_if_value_type`
   growing collection support, touching MIR lowering plus both backends.
3. A deep copy on every struct assignment reintroduces exactly the O(n)-per-write
   hazard `.claude/rules/code-style.md` warns about, at scale, across all 14k+
   files. The correct shape is refcount-based COW in the JIT's runtime
   representation, not eager deep copy — a runtime-representation change, not a
   patch.

Per the escalation rule in the task ("a half-fix to value semantics in a
self-hosting compiler is far worse than a well-documented bug"), no fix was
attempted.

### Where a fix belongs

**Both, and the seed alone is not enough.** The measured defect is in the Rust
seed's MIR/codegen (`src/compiler_rust/compiler/src/mir/`). The pure-Simple
compiler carries its own MIR layer (`src/compiler/50.mir/`) and its own copy
lowering; whether it reproduces the defect is **UNTESTED** — no full-CLI
pure-Simple binary is deployed, and a self-hosted retest is blocked by the
bootstrap redeploy. A seed-only fix would not fix the self-hosted compiler.
Do not close this on a seed-only fix.

### Practical guidance until fixed

The `ecc_page_clone`-style explicit array-rebuilding workarounds already landed
in `fw/` remain necessary. Extend the same caution to **top-level `Dict`
assignment** and to **nested arrays**, which the original record did not cover.
Running a suspect test under `SIMPLE_EXECUTION_MODE=interpreter` is a cheap way
to tell a real assertion failure from a JIT aliasing artifact.

---

## Blast radius MEASURED — 11 of 16 shapes alias (parent-verified 2026-09-01)

Probe `test/cow_probe.spl`, run by the parent on the default `bin/simple run` lane.
This supersedes the "scope not established" note above.

| # | shape | result |
|---|---|---|
| 1 | struct nested `[i64]` via var assign | **ALIASED** |
| 2 | top-level `[i64]` assign (baseline) | COW-OK |
| 3 | struct nested struct value | COW-OK |
| 4 | struct nested `Dict` | **ALIASED** |
| 5 | top-level `[Struct]` element field write | **ALIASED** |
| 6 | struct nested `[Struct]` element field | **ALIASED** |
| 7 | struct by-value **fn arg**, nested array | **ALIASED** |
| 8 | array extracted from struct field into a local | COW-OK |
| 9 | local array into struct ctor, then mutate the local | **ALIASED** |
| 10 | **returned struct** then copy | **ALIASED** |
| 11 | nested `[[i64]]` outer assign | **ALIASED** |
| 12 | struct scalar field (baseline) | COW-OK |
| 13 | **class** nested `[i64]` via var assign | **ALIASED** |
| 14 | class nested array via method | **ALIASED** |
| 15 | **`val`-to-`val`** struct nested array | **ALIASED** |
| 16 | struct nested array, WHOLE-field replace | COW-OK |

Variants (`test/cow_probe_variants.spl`): scalar-write-first-then-index ALIASED;
three-way share ALIASED; replace-field-then-index COW-OK.

### The rule that actually holds

**Any *interior* collection aliases.** Structs, classes, function arguments,
return values, nested `[[i64]]`, `[Struct]` elements and nested `Dict` are all
affected, and `val` does not protect. Only a **freshly constructed** array is
safe (#2, #16, variant E) — an *inherited* array aliases even after the enclosing
fields map has already diverged.

This is a **value-model defect, not a struct-assignment bug**. The originally
filed title understates it and should be read accordingly.

### Still untested — do not assume safe

The native/AOT lane (3 build attempts failed or did not finish on a saturated
host) and a forced tree-walk interpreter — no flag disambiguates it:
`SIMPLE_BACKEND` selects the codegen backend only (`codegen.rs:3019`),
`SIMPLE_JIT_STRICT` only gates unresolved symbols (`jit.rs:172`).

## Mechanism — candidates located, NOT pinned

- `Value::Array(Arc<Vec<Value>>)`, `Object{fields: Arc<HashMap<..>>}`
  (`compiler/src/value.rs:1473,1516`). There is **no deep copy anywhere**;
  "value semantics" is emergent from `Arc::make_mut` at write time only.
- `interpreter/place.rs:146 step_mut`, `:253 write_place` and the
  `node_exec.rs:1583+` Object arm read as COW-**correct**, and the unit test
  `place.rs:397 write_through_alias_does_not_leak_into_the_copy` **passes** —
  contradicting the observed behaviour. So the lane executing `run` is probably
  not this code.
- The leading hypothesis (`node_exec.rs:1401-1409 case2_unique`, a top-level-only
  `strong_count==1` check) is **empirically killed** by variant A.
- Non-recursion is deliberate somewhere: `interpreter_call/core/arg_binding.rs:24-38`
  copies value types but explicitly does **not** recurse into a struct's
  array/dict fields.

**Next experiment:** an instrumented seed build (COWDBG eprintln at
`case2_unique`, the Object arm, and `write_place`). Written but never completed —
a cold `cargo build --release` did not finish against 16 competing cargo jobs.

## Fix location and why no fix was attempted

Both the Rust seed and the pure-Simple compiler: the seed is bootstrap-only, so a
seed-only fix leaves the self-hosted compiler broken; a self-hosted retest is
blocked on the bootstrap redeploy.

With 11+ aliased shapes spanning structs, classes, args, returns, nested arrays
and Dicts, this is a **value-model change, not a local patch**. A speculative fix
could silently alter behaviour across ~14,000 files, so none was attempted —
deliberately.

## Working guidance until fixed

Treat every interior collection as shared. When a copy is intended, construct a
fresh array explicitly or replace the whole field (#16 is COW-OK). Do not rely on
assignment, argument passing, or return values to copy. Note that
`.claude/rules/code-style.md`'s COW *performance* warning describes a mechanism
that, for interior collections, does not fire at all.

---

## DECISIVE REFINEMENT — this is TWO bugs, and the lane is the discriminator

**Parent-verified 2026-09-01.** The deployed binary has an undocumented lane
selector, `SIMPLE_EXECUTION_MODE` (`interpreter | cranelift-jit | native`).
Re-running the identical probe under each lane splits the finding in two:

| lane | ALIASED shapes (of 16) |
|---|---|
| default `bin/simple run` (cranelift JIT) | **11** |
| `SIMPLE_EXECUTION_MODE=interpreter` | **1** (case 7 only) |

Variants A-E: default 4 of 5 ALIASED; interpreter **all five COW-OK**.

### Bug 1 — the JIT lane does not implement value semantics for interior collections

11 broken shapes, and this is the lane `bin/simple run` selects by DEFAULT.

The severity is not only the aliasing. **The two engines disagree on language
semantics**, so the same program means different things depending on which
engine is selected — and the selection can change under JIT demotion
(`[engine-demotion]` messages are routine in this tree). A program can therefore
change meaning between runs.

### Bug 2 — the interpreter has exactly one broken shape, and it is deliberate

Case 7 (struct passed **by value as a function argument**, nested array) aliases
on both lanes. **CITATION WITHDRAWN (2026-09-01):** an earlier draft cited
`interpreter_call/core/arg_binding.rs:24-38` as the mechanism. **That file does
not exist in this worktree** — the citation came from a sibling agent worktree
and is withdrawn as unverified here.

What IS verifiable in this tree: `src/compiler_rust/compiler/src/perf_counters.rs:25`
declares counters for `copy_value_type_in_place (argument binding, value-type
struct copy)` — `VT_CALLS`, `VT_ARRAY_ELEMS_SCANNED`, `VT_ARRAY_CLONES`,
`VT_ARRAY_ELEMS_CLONED`, `VT_OBJECT_FIELD_CLONES`. So the value-type
argument-copy machinery is *referenced* from here while its implementation lives
elsewhere. Case 7 is probably small and contained, but its mechanism is
**not established** and must not be described as documented-deliberate.

### What this vindicates

`interpreter/place.rs:146/:253` and the `node_exec.rs:1583+` Object arm read as
COW-**correct**, and their alias unit test at `place.rs:397` **passes**. That
apparent contradiction is now explained: **that code was never the lane executing
the probe.** The earlier "mechanism not pinned" conclusion was correct to stop
where it did rather than force a story.

## Hard blocker on fixing Bug 1

**The deployed `bin/simple` is not built from this worktree.**
`SIMPLE_EXECUTION_MODE`, `[engine-receipt]`, `[engine-demotion]` and
`cranelift-jit` all appear as strings in the binary but in **no `.rs` or `.spl`
source under `src/`** — only in `.smf` artifacts and a sibling tree
(`.claude/worktrees/agent-a32f503a1c9897874/`). The JIT lane's source is not in
this tree, so its mechanism cannot be cited or patched from here. Identifying
where `cranelift-jit` actually lives is the prerequisite for any fix.

## Interim mitigation available TODAY

```sh
SIMPLE_EXECUTION_MODE=interpreter bin/simple run <file>
```

restores correct value semantics for **15 of 16 shapes**. Use it for any code
where interior-collection copy semantics are load-bearing — and note that
results measured on the default lane may be wrong in that respect.

## Still untested

The native/AOT column. Four builds attempted: one killed by a separate seed
codegen defect (`unsupported LLVM value conversion from i64 to void`), the rest
starved by ~12 competing `native-build` jobs. **Do not assume the native lane
matches either column.**


---

## Probe files

The 16-case probe, its 5 discriminating variants, and a native-lane variant were
written as plain runnable programs (`cow_probe.spl`, `cow_probe_variants.spl`,
`cow_probe_native.spl`). They are **deliberately not committed**: they carry no
docstring, `@cover` tag, or `describe` block, so they are diagnostics rather than
specs and do not belong under `test/`.

Everything needed to reproduce is inline in this record — the 6-line minimal case
above, the full 16-row result table, and the per-lane split. Anyone fixing the JIT
lane can rebuild the probe from this document in a few minutes; a reader does not
need the files.

If they are re-created for a fix, give them spec structure and a home outside
`test/`, or the repo's idiom ratchet will reject them (measured: they fail
`Code Idiom & Structural Ratchet Gates`).
