# Stage-2 `compile --format=smf` SIGSEGV on arm64-darwin is a 32-bit `~7` mask, NOT the dict.values() field-index collapse (2026-08-24)

## Verdict

Two lanes reported contradictory things about the same rc=139. **Both observations
are correct; the conflation of the two defects was the error.**

* **Lane A** (arm64-darwin): `<stage2> compile h.spl --format=smf` on a
  three-line hello world returns **rc=139**, faulting in
  `hir_codec.hc_enc_hir_module + 1452`. **CONFIRMED, reproduced here.**
* **Lane B** (arm64-darwin): the `for x in dict.values()` field-index corruption
  does **not** reproduce on this host; `SIMPLE_MIR_FIELD_TRACE=1` shows
  `field-idx-fallback0` firing **0 times**. **CONSISTENT** — that probe watches
  `resolve_field_index` falling back to offset 0, and this crash never reaches
  it.
* **Therefore:** the arm64 rc=139 is a **different defect** from the x86_64-linux
  `dict.values()` offset-0/i64 collapse. Same *family* (a for-loop variable over
  a `Dict` projection loses its element type), different *consequence* (integer
  **width** collapse to i32, not field index collapse to 0).

It is also **not** the "malformed word passes a shape test" reading recorded in
`7c453e7b076` for `lower_hir_block`. At this site the guarded word is a
**perfectly well-formed** tagged heap reference. The guard's *test* passes
correctly; the guard's *mask* is the wrong width.

## The defect, from disassembly (measured, not inferred)

Binary: `build/bootstrap/stage2/aarch64-apple-darwin/simple`,
sha256 `8cc20c89ab48e65ca8e8059f6b461301eea409a8cc920d266b3cf37167f2d97c`
(the admitted Stage-2 trust root built 2026-08-24 13:52 at HEAD `cde14a397aa`).

```
+1368: bl   rt_index_get            ; ks3[i]
+1372: bl   rt_value_unbox_int      ; <-- unboxes a SymbolId STRUCT as an int
+1376: mov  x23, x0                 ; x23 = 0x0000000c43060e01  (sound: tag=1=HEAP)
+1380: and  x22, x0, #0xffffffff    ; <-- 32-bit truncation for the nil test
+1388: cmp  x22, #0x3               ; nil sentinel
+1420: bl   rt_alloc  (#8 = 1 word) ; CoW clone of SymbolId
+1424: and  x8,  x23, #0x7          ; tag
+1428: cmp  x8,  #0x1               ; == HEAP ?      -> true
+1436: ands x9,  x23, #0xfffffff8   ; <-- 32-BIT MASK. x9 = 0x0000000043060e00
+1440: cset w10, ne                 ;    (v & ~7) != 0 ?  -> true
+1448: csel x8,  x9, x0, ne         ; x8 = TRUNCATED pointer
+1452: ldr  x8,  [x8]               ; *** SIGSEGV ***
+1464: and  x8,  x0, #0xfffffffffffffff8   ; <-- the CORRECT 64-bit mask, same fn
```

`x23 = 0xc43060e01` is a valid tagged heap ref (base `0xc43060e00`, tag 1). The
high half `0xc` is destroyed by the 32-bit mask, and the resulting
`0x43060e00` is unmapped. **The fault address tracks ASLR across runs**
(`0x3060e00`, then `0x43060e00`, with x0 correspondingly `0x9...` then
`0xc...`) — proof that a live pointer is being truncated, not that a garbage
word is being dereferenced.

## Why the value is typed i32

`rt_value_unbox_int` at +1372 is the tell: the loop variable is being unboxed as
an **int**, though `struct SymbolId: id: i64` (`hir_types.spl:101`) is a 1-word
struct. Source (`src/compiler/20.hir/generated/hir_codec.spl`,
`hc_enc_hir_module`):

```
val ks3 = if node.functions == nil: [] else: node.functions.keys()
w.put_i64(ks3.len())
for dk3 in ks3:
    if dk3 == nil: w.put_i64(0)
    else:
        w.put_i64(1)
        hc_enc_symbol_id(w, dk3)     # <- by-value pass emits the 1-word CoW clone
```

`node.functions` is `Dict<SymbolId, HirFunction>`. The loop variable `dk3` over
`.keys()` loses its `SymbolId` type, is treated as `int`, and every derived
operation — the nil compare and the CoW-clone guard — is emitted at **32-bit**
width. `.keys()`, not `.values()`, which is why the `.values()`-targeted probes
found nothing.

## Whole-binary census (mechanical)

`objdump -d` over the same stage-2 binary, counting 64-bit-register operands:

| mask | `and` | `ands` |
|---|---|---|
| `#0xfffffff8` (32-bit, WRONG) | 367 | **7** |
| `#0xfffffffffffffff8` (64-bit, correct) | 22,382 | 29,298 |

All **7** `ands`-form (flag-setting, i.e. the clone-guard shape) 32-bit-mask
sites are in **one** function, `hc_enc_hir_module`, all on `x23`. The correct
mask outnumbers the wrong one ~138:1, so this is a localized type-width defect,
not the prevailing lowering.

Also 92 sites of `and xN, xN, #0xffffffff` (the 32-bit nil-compare truncation).

## Reproducer

```sh
printf 'fn main()\n    print("hi")\n' > h.spl
build/bootstrap/stage2/aarch64-apple-darwin/simple compile h.spl --format=smf
rc=$?    # 139, deterministic
```

Last log line before the fault is
`[bootstrap-error-count] source_idx=0 point=post-diagnostics count=0`; the
crash is inside `hir_cache_store` -> `hir_module_encode` -> `hc_enc_hir_module`.
Backtrace frames 1-5: `hir_module_encode+344`, `hir_cache_store+424`,
`CompilerDriver.lower_and_check_impl+9176`, `CompilerDriver.compile+1916`,
`run_compile_bootstrap+572`.

## NOT established here

* Whether a Stage 2 built fresh from `origin/main` (`ee98a2c3222`, 96 commits
  ahead of the tested binary's `cde14a397aa`) still emits the 32-bit mask.
* Which component chooses the width (seed HIR typing vs MIR vs the arm64
  backend's immediate materialization).
* Whether this is latent rather than absent on x86_64-linux. No claim is made
  about where `rt_alloc` maps there.
* Whether fixing this also clears the `substitute_stmt` / `lower_hir_block`
  crashes. They share the guard *shape*; only this site was shown to carry a
  wrong-width mask.

## CONFIRMED at `origin/main` — the task's literal discriminator, executed

A Stage 2 was built fresh from `origin/main` (`ee98a2c3222`, i.e. WITH the
Mach-O link fix) in an isolated clean worktree via the sanctioned lane
`bootstrap-from-scratch.sh --strategy=adhoc --full-bootstrap --stop-after-stage2`,
backend `llvm`. It was **admitted** — the wrapper printed
`Stage 2 admitted; stopping before Stage 3 as requested.` and wrote both
`stage2-provenance.receipt` and `stage2-sanity.receipt`.

| | tested stage 2 (`cde14a397aa`) | fresh stage 2 (`origin/main`) |
|---|---|---|
| sha256 | `8cc20c89ab48e65c…` | `1db26649ff88eeb9…` |
| built | 2026-08-24 13:52 | 2026-08-24 17:38 |
| `compile h.spl --format=smf` | **rc=139** | **rc=139** |
| fault frame | `hc_enc_hir_module + 1452` | `hc_enc_hir_module + 1452` |
| guarded word (x23) | `0x0000000c43060e01` | `0x0000000c7ec24d01` |
| truncated ptr (x8) | `0x0000000043060e00` | `0x000000007ec24d00` |
| `ands x*, x*, #0xfffffff8` | 7, all in `hc_enc_hir_module` | 7, all in `hc_enc_hir_module` |
| `and x*, x*, #0xfffffff8` | 367 | 367 |
| correct 64-bit mask (and+ands) | 51,680 | 51,666 |
| `field-idx-fallback0` | — | **0**, in every build log |

**The defect is unchanged at `origin/main`.** The 96 commits between the two
trees — including `7c453e7b076` (HirBlock clone containment),
`0299186137d`, `467f8f66757` — do not touch it.

`SIMPLE_MIR_FIELD_TRACE=1` was set for the entire fresh build; `field-idx-fallback0`
appears **0 times** across `stage2-native-build.log`, `rust-seed-build.log`,
`rust-native-all-build.log`, `rust-runtime-nolto-build.log`, and
`rust-compiler-backfill-build.log`. That is Lane B's observation, reproduced on
the exact binary that also reproduces Lane A's rc=139 — the two coexist, which
is the whole point.

## Where the 32-bit mask comes from — the emitter is NOT at fault

`emit_aggregate_block_copy`
(`src/compiler_rust/compiler/src/codegen/llvm/functions/objects.rs:154-289`) is
the emitter of this exact sequence, and its mask is correct:

```rust
let i64_type = self.runtime_int_type();          // i64 here: pointer_width()==64
let tag_mask   = i64_type.const_int(7, false);
let untag_mask = i64_type.const_int(u64::MAX - 7, false);   // 0xFFFFFFFFFFFFFFF8
```

Byte-identical at `cde14a397aa` and at `origin/main`. The 32-bit immediate in
the machine code is an **instcombine fold, not an emitted constant**:

```
zext(trunc_i32(v)) & 0xFFFFFFFFFFFFFFF8   ==   v & 0x00000000FFFFFFF8
```

LLVM legitimately rewrites the pair into one 64-bit `AND` against
`0xfffffff8` and drops the intermediate. The companion
`and x22, x0, #0xffffffff` at +1380 is the *other* half of the same
`zext(trunc(...))` pair, left behind for the nil compare.

**So the defect is upstream typing, not codegen arithmetic.** A value that is a
64-bit tagged heap handle is being narrowed to `i32` and widened back. Any fix
that only widens the mask would paper over it; the loop variable's type is what
is wrong.

This also means the seed's `objects.rs` needs no change, and the
`lower_hir_block` reading in `7c453e7b076` ("a malformed word passes a shape
test") does not describe this site: here the word is sound and the *guard
expression itself* has been narrowed.

## Incidental finding: the seed's own hosted `native-build` still cannot link on macOS

`ee98a2c3222` changed exactly one code file, the pure-Simple
`src/compiler/70.backend/backend/llvm_native_link_hosted_support.spl`.
`src/compiler_rust/**` contains no occurrence of `__simple_startup_before_main`
at all. Measured with the seed
`src/compiler_rust/target/bootstrap/simple` (built 2026-08-24 13:34):

```
native-build r.spl  with SIMPLE_PROJECT_ROOT=<pre-fix tree>   -> FAIL
native-build r.spl  with SIMPLE_PROJECT_ROOT=<origin/main>    -> FAIL (same)

Undefined symbols for architecture arm64:
  "___simple_startup_before_main", referenced from:
      _main in simple_entry.o
```

The seed's `native-build` link route does not consume the fixed `.spl`, so
hosted `native-build` **through the seed** on macOS remains broken after
`ee98a2c3222`. This does not block the bootstrap wrapper (Stage 2 links through
a different route and succeeded), but it does block ad-hoc seed-driven native
reproducers on this host. Not filed separately; recorded here.

## macOS harness note

`setsid(1)` does not exist on Darwin and the native-build worker spawns through
it as `setsid -w <cmd>`, so a shim must both exist and strip setsid's own flags:

```sh
#!/bin/sh
while [ $# -gt 0 ]; do
  case "$1" in -w|--wait|-f|--fork|-c|--ctty) shift ;; --) shift; break ;; -*) shift ;; *) break ;; esac
done
exec "$@"
```

A naive `exec "$@"` shim fails with `exec: -w: invalid option`.

## `SIMPLE_HIR_CACHE=0` clears the SEGV — and is NOT a usable workaround

The kill switch at `driver_hir_cache.spl:78` bypasses `hir_cache_store`, which
is the only caller of `hir_module_encode` on this path. Measured on the same
crashing stage-2 binary and the same `h.spl`:

```
             <stage2> compile h.spl --format=smf   -> rc=139 in ~0.5 s
SIMPLE_HIR_CACHE=0 <stage2> compile h.spl --format=smf   -> no SEGV
```

That independently confirms the localization: the fault is reached only through
the HIR cache store, not through lowering or codegen generally.

It does not, however, produce an artifact. With the cache off the run reaches
`[DEBUG] AOT SMF: compiling to h.smf (backend: llvm)` and then **runs away**:
killed after **>11 minutes** of continuous 100% CPU at ~1.3 GB, with no `h.smf`
written. `sample(1)` over 5 s, 3,732 of 3,732 main-thread samples:

```
compiler__mir_opt__mir_opt__storage_projection_lowering__lower_mir_storage_project_fields_v1 + 252
  3484  rt_range + 80
   123  rt_range + 76
    98  rt_array_push_grow + 8
```

A single `rt_range` inside `lower_mir_storage_project_fields_v1` growing an
array without terminating. Plausibly the same bad-integer family (a garbage or
truncated bound reaching `range`), but **not diagnosed** — recorded as a
second, independent stage-2 defect, not as evidence for the first.

Net: there is no known flag that makes this stage-2 binary compile a
three-line hello world.

---

# LOCALIZED TO `src/compiler_rust` — the Simple-side lowering is NOT the code that builds Stage 2 (2026-08-24, later the same day)

## Verdict

**The defect this record documents lives in the Rust seed, not in
`src/compiler/50.mir/**`.** A 1.7-second runnable reproducer now exists. The
narrowing mechanism is the **value-position `if` merge** — `if cond: [] else:
d.keys()` — and it is confirmed by a positive/negative pair on the same binary
and the same fixture.

## Why the Simple-side fix does not reach Stage 2

`scripts/bootstrap/bootstrap-from-scratch.sh:3499` and `:3511` set
**`SIMPLE_NATIVE_BUILD_RUST=1`** on the Stage-2 `native-build`. Per the seed's
own source, `driver/src/cli/native_build.rs:603`:

> "this Rust handler is reached only via `SIMPLE_NATIVE_BUILD_RUST=1` or a
> cross-target executable build (see `dispatch_command` in
> `driver/src/main.rs`) -- plain `bin/simple native-build` runs the pure-Simple
> driver instead (`src/compiler/80.driver/driver_aot_native_output.spl`)"

(dispatch: `driver/src/main.rs:168-172`.) So Stage 2's 750 modules are lowered
and codegen'd entirely by `src/compiler_rust`. Measured directly on one fixture,
one seed binary, changing only that env var:

| path | probe lines | result |
|---|---|---|
| plain `native-build` (pure-Simple driver) | 4 | rc=0, correct |
| `SIMPLE_NATIVE_BUILD_RUST=1` (Rust handler) | **0** | **rc=139** |

Zero probe lines is the direct evidence: `SIMPLE_TRACE_DICT_ELEM=1` instruments
`src/compiler/50.mir/**`, and that code never runs on the Stage-2 path.

A Stage 2 WAS built from a tree carrying the Simple-side merge fix
(commit `c1f1ade8bc4`, sanctioned lane, `--stop-after-stage2`, admitted, sha256
`4a2dba4e58459a44ae4bd19e8a0e083404fe9c4248ba77eb5d05d0ce0863d9de`). It still
returns **rc=139**, and the census is unchanged: **7** `ands x*, x*,
#0xfffffff8`, all still inside `_compiler__hir__generated__hir_codec__hc_enc_hir_module`,
with the instruction sequence byte-identical to the one at the top of this
record. That is the experiment that proves the localization, not an inference.

## The reproducer — 1.7 s, no bootstrap

```sh
cat > b2.spl <<'SPL'
struct SymbolId:
    id: i64
class Node:
    functions: Dict<SymbolId, i64>
fn enc_sym(node: SymbolId) -> i64:
    node.id
fn enc_node(node: Node) -> i64:
    val ks3 = if node.functions == nil: [] else: node.functions.keys()
    var acc = ks3.len()
    for dk3 in ks3:
        if dk3 == nil:
            acc = acc + 0
        else:
            acc = acc + 1000 + enc_sym(dk3)
    acc
fn main():
    var d: Dict<SymbolId, i64> = {}
    d[SymbolId(id: 7)] = 100
    d[SymbolId(id: 9)] = 200
    print("total={enc_node(Node(functions: d))}")
SPL

SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_BOOTSTRAP=1 SIMPLE_PROJECT_ROOT=<repo> \
  <seed> native-build --backend llvm --source . --entry b2.spl -o b2llvm
./b2llvm; echo $?      # 139, deterministic, no output
```

Two harness notes: `fn main()` in newline-block form is rejected by the Rust
handler's discovery parser (`expected expression, found Indent`) — write
`fn main():`. And `setsid(1)` does not exist on Darwin; the shim in the macOS
note above is still required.

Generated code, `_b2__enc_node` — the SAME sequence as `hc_enc_hir_module`:

```
bl   _rt_alloc                     ; #8
and  x8, x22, #0x7                 ; tag
cmp  x8, #0x1
cset w8, eq
ands x9, x22, #0xfffffff8          ; <-- 32-BIT MASK
cset w10, ne
tst  w8, w10
csel x8, x9, x0, ne
ldr  x8, [x8]                      ; *** SIGSEGV ***
```

`objdump -d`: exactly **1** `ands ..., #0xfffffff8` and **9**
`rt_value_unbox_int` call sites.

## The discriminator: it is the `if` MERGE, on this path too

Same file, same command, only the binding changed:

| binding | rc | 32-bit masks |
|---|---|---|
| `val ks3 = if node.functions == nil: [] else: node.functions.keys()` | **139** | 1 |
| `val ks3 = node.functions.keys()` | **0** (`total=2018`, correct) | **0** |

So the `.keys()` lowering on the Rust path produces a correct element type; the
value-position `if` merge throws it away, exactly as the pure-Simple lowering did
before it was fixed. The then-arm is an EMPTY array literal — it has no element
to take a type from — and it wins the merge.

**Candidate site, named but NOT confirmed by measurement:**
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_control.rs:69`
`lower_if_expr` types the merge slot from `expr_ty`, the HIR-inferred type of the
whole if-expression, and stores both arms into it with that same `ty`. If the
HIR type of `if …: [] else: d.keys()` is inferred from the empty-literal arm,
that is where the i64 element type enters. This was read, not proven; the next
lane should confirm against the reproducer before editing.

## What was fixed, and where it does apply

The identical defect in the pure-Simple lowering (`lower_if` / `lower_if_chain`
in `src/compiler/50.mir/mir_lowering_stmts.spl`) was found first, by the probes
below, and IS fixed. That path is the DEFAULT tooling path — plain
`bin/simple native-build` — so the fix is load-bearing there even though it does
not touch Stage 2. Fixture: rc=139 -> rc=0 with the correct value; and
`(if d == nil: [] else: d.keys()).len()` 0 -> 2.

### Probe output (the discriminator that found it)

`SIMPLE_TRACE_DICT_ELEM=1`, default OFF, both ends of the dataflow:

```
# `val ks = if d == nil: [] else: d.keys()`      <- the real shape
[dict-elem] method=keys recv_mir_type=Dict(Struct(...),I64) stamped_elem_type=Struct(...)
[dict-elem] for-in coll_mir_type=Array(I64,0) element_type=I64          <- LOST at the merge

# `val ks = d.keys()`                             <- no merge
[dict-elem] method=keys recv_mir_type=Dict(Struct(...),I64) stamped_elem_type=Struct(...)
[dict-elem] for-in coll_mir_type=Array(Struct(...),0) element_type=Struct(...)
```

The stamp was always correct — which is why every `.values()`-targeted probe in
the earlier lanes found nothing, and why `field-idx-fallback0` legitimately fires
0 times. Confirmed for a class-valued dict (`Dict<SymbolId, HirFunction>`) and
for a receiver whose class lives in an imported module: both recover
`Dict(Struct, …)` correctly, so receiver-type recovery is NOT implicated.

Second half, same change: the merge result temp comes from `new_temp` and belongs
to no marking set, so `.len()` on an `Array(elem, 0)` local took the STATIC size
path and answered 0 while the same local iterated N elements — `direct=2
merge=0`. `hc_enc_hir_module` does `w.put_i64(ks3.len())` immediately before each
such loop, so this would have written a 0 count ahead of N records. Fixed by
mirroring the arm's `runtime_array_locals`/`runtime_dict_locals` onto the merge
slot; `direct=2 merge=2` after.

## Corrections to earlier sections of this record

* The "Incidental finding: the seed's own hosted `native-build` still cannot link
  on macOS" section is **RESOLVED at `origin/main`**. The Mach-O weak-DEFINITION
  fix (a weak `__simple_startup_before_main` under `#if defined(__APPLE__)`)
  landed in `llvm_native_link_hosted_support.spl`. Independently re-derived here
  before that was noticed, with a two-TU clang probe confirming both halves:
  `__attribute__((weak_import))` on a bare declaration does **not** satisfy ld64,
  a weak definition does, and a strong definition in another object overrides it.
* The "LLVM emitter is NOT at fault" section is **confirmed and explained**: the
  emitter's mask really is 64-bit; instcombine folded `zext(trunc_i32(v)) & ~7`
  because the VALUE was narrowed upstream, at the `if` merge.

## Still NOT verified

* Whether the `> 11 min` runaway in `lower_mir_storage_project_fields_v1` under
  `SIMPLE_HIR_CACHE=0` is the same root cause. Not retested.
* Stage 3 and beyond. Not attempted; a separate lane owns the
  `phase4:monomorphize` blocker.
* x86_64-linux. Every measurement here is aarch64-apple-darwin.
* `for e2 in (node.domain_blocks ?? [])` in the real codec. A minimal `?? []`
  fixture fails differently (loud for-in panic) and the discrepancy was not
  chased — see `if_merge_collection_identity_residual_2026-08-24.md`.

---

# CONFIRMED AND FIXED IN THE SEED — the site is HIR `lower_if`, not MIR `lower_if_expr` (2026-08-24)

## Verdict

PASS — mechanism confirmed at a named site, fixed, and measured on a
same-profile before/after pair of seed binaries. The candidate named in the
section above (`mir/lower/lowering_expr_control.rs:69` `lower_if_expr`) is NOT
the site; it is downstream of it and could never have fixed the loop. Following
the evidence instead:

**`src/compiler_rust/compiler/src/hir/lower/expr/control.rs`, `Lowerer::lower_if`**
— which carried the defect in its own doc comment: *"Result type is taken from
the then branch."*

## The chain, each link read in the source

1. `lower_array` (`hir/lower/expr/collections.rs:80-87`) types an EMPTY array
   literal as `Array { element: type_inference_config.empty_array_default,
   size: Some(0) }`. That default is **`TypeId::I32`**
   (`type_inference_config.rs:33`) — this is where the *i32* in this record's
   title literally comes from.
2. `.keys()` on a typed dict is stamped correctly:
   `Array { element: K, size: None }` (`hir/lower/expr/mod.rs:1615-1618`).
3. `lower_if` set `ty = then_hir.ty` and dropped the else arm entirely, so
   `val ks3 = if …: [] else: d.keys()` got `Array { I32, Some(0) }`.
4. The Let stmt gives that TypeId to the local, and
   `lower_for_stmt` (`mir/lower/lowering_stmt.rs:1710-1745`) reads
   **`iterable.ty`** — not the MIR merge slot — classifies the element as I32,
   and emits `UnboxInt` followed by `UnitNarrow { to_bits: 32, signed: true }`.
5. On a 64-bit tagged heap handle that destroys the high half; LLVM folds
   `zext(trunc_i32(v)) & ~7` into one `and #0xfffffff8` and the truncated
   pointer is dereferenced.

Step 4 is why `lower_if_expr`'s merge slot was the wrong suspect: the for-loop
never consults it. In the seed the HIR TypeId is the ONLY carrier of array
identity — there is no `runtime_array_locals` side table as in the pure-Simple
lowering — so the same TypeId also decides `.len()`.

## The fix

`merge_if_arm_types` in `control.rs`, applied in both `lower_if` and
`lower_if_let_expr`. When exactly one arm has the untyped-empty-literal
signature (`element == empty_array_default && size == Some(0)` — the same
predicate the existing `push`/`append` receiver refinement at
`hir/lower/expr/mod.rs:797` already uses) and the other arm is an array with an
informative element, the informative arm's TypeId is adopted **wholesale**,
in both directions. Everything else is unchanged, so a genuinely i32-element
array is never retyped.

Wholesale rather than the pure-Simple fix's element-only refinement because
here the type is the only carrier: keeping the empty literal's `size: Some(0)`
would leave `.len()` on the merged local answering a static 0 while the same
local iterates N elements — the second half of the same defect. Adopting
`Array { K, None }` fixes both halves at once, which the reproducer's
`total=2018` (2 from `.len()` + 1007 + 1009) verifies directly.

`elif` needs no separate arm: the parser desugars it to a nested `If` in the
else slot, so the merge recurses outward. Measured, not assumed (below).

## Measurements

Two seed binaries, SAME cargo profile and features
(`cargo build --locked --offline --release -p simple-driver --features llvm`,
LLVM 18, aarch64-apple-darwin), differing only in `control.rs`; each fixture
built under its own `SIMPLE_CACHE_SCOPE`.

| binary | md5 | fixture | rc | `ands #0xfffffff8` | output |
|---|---|---|---|---|---|
| origin/main | `e541abdf58866f93f1aa570cafea23e4` | `b2.spl` (if-merge) | **139** | **1** | — |
| fixed | `ae375eeb3bd7fa46fbd5ab949cea624e` | `b2.spl` | **0** | **0** | `total=2018` |
| origin/main | `e541abdf…` | `b2ok.spl` (no merge, control) | 0 | 0 | `total=2018` |
| fixed | `ae375eeb…` | `b2ok.spl` | 0 | 0 | `total=2018` |
| origin/main | `e541abdf…` | `elif.spl` (`[] elif [] else keys()`) | **139** | **1** | — |
| fixed | `ae375eeb…` | `elif.spl` | **0** | **0** | `total=2018` |

The fixed build is reproducible: rebuilt twice, same md5 both times.

Regression fixture (`reg.spl`: value-position `if` over text / int / array of
int / array of text / a 3-arm `elif` chain, every arm well-typed) — `objdump
-d` of the produced binary is **identical** before and after apart from the
`file format` header line naming the file (2 diff lines, both the header). Same
program output `t=yes i=1 a0=1 s0=a e=three` on both.

## Explicitly NOT verified here

* Stage 2. See the following section for its status.
* x86_64-linux. Every measurement above is aarch64-apple-darwin.
* The two residual defects in
  `if_merge_collection_identity_residual_2026-08-24.md` (`x ?? []` loses
  collection-ness; a function-RETURNED if-merge array reads len 0). Neither is
  addressed: `??` is a different construct, and a returned array's TypeId is
  the callee's declared return type, which this merge never sees.

## Stage 2 — MEASURED after the seed fix: the SIGSEGV is GONE, hello world still does not compile

Verdict: **PARTIAL.** `rc=139` -> `rc=1` with a clean diagnostic, and all 7
32-bit masks are gone from `hc_enc_hir_module`. This is NOT "Stage 2 is fixed":
a second, previously-invisible codec defect is now the blocker.

Stage 2 built from a tree carrying only the seed fix
(`sh scripts/bootstrap/bootstrap-from-scratch.sh --strategy=adhoc
--full-bootstrap --stop-after-stage2 --output=<dir>`, aarch64-apple-darwin,
750 modules compiled / 0 failed, sha256
`aaac7c6270b501a3200eab644971cda0d825ae53a5ad73b238c37ccc14f8b7b5`).
Both gates on that binary report `status=pass`: `stage2-sanity.env`
(5 checks) and `stage2-receiver.env`
(`bootstrap_stage2_struct_receiver=PASS`).

Same fixture, same env, both binaries:

```
printf 'fn main()\n    print("hi")\n' > h.spl
SIMPLE_BOOTSTRAP=1 SIMPLE_PROJECT_ROOT=<repo> <stage2> compile h.spl --format=smf
```

| stage2 | sha256 | rc | `ands #0xfffffff8` total | ... inside `hc_enc_hir_module` |
|---|---|---|---|---|
| pre-fix (sibling lane's admitted build) | `e6761bfe…` | **139** (SIGSEGV, no message) | 524 | **7** |
| post-fix | `aaac7c62…` | **1** (clean error) | 517 | **0** |

524 - 517 = 7 — exactly the seven this record's first section counted, and they
are exactly the ones inside `hc_enc_hir_module`. The remaining 517 are
elsewhere in the binary and are legitimate 32-bit arithmetic.

The new, now-reachable failure is a different defect:

```
[bootstrap-error-count] source_idx=0 point=post-diagnostics count=0
error: hir codec: no `HirTypeKind` arm for tag -1; regenerate
       src/compiler/20.hir/generated/hir_codec.spl
```

That text comes from the **encoder's** catch-all,
`hc_enc_hir_type_kind`'s `case _: hc_bad_tag("HirTypeKind", -1)`
(`src/compiler/20.hir/generated/hir_codec.spl:5378`) — a `HirTypeKind` variant
that no `case` in the generated encoder matches. It is a codec-completeness /
match-dispatch problem, unrelated to pointer truncation, and it was
unreachable before because the process died first. It is now the Stage-2
blocker and needs its own lane.

### Admission caveat, stated rather than hidden

This run did NOT get an admission receipt: it ended
`error: refused incomplete Stage 2 admission provenance` (exit 4). The cause is
recorded and is a concurrency artifact, not a property of the fix — the guard
compares a source snapshot taken before and after the stage, and exactly **3**
files changed under the shared worktree mid-run:
`src/compiler/50.mir/mir_types.spl`,
`src/compiler/50.mir/mir_lowering_stmts.spl`, and
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` — a parallel
session editing the pure-Simple lowering. `tool-authority` and `runtime-origin`
snapshots are byte-identical before and after, and both stage-2 evidence files
say `status=pass`. None of those three files is on the Stage-2 build path
(`SIMPLE_NATIVE_BUILD_RUST=1` never executes `src/compiler/50.mir/**`), so the
binary itself is sound evidence; it is simply not an *admitted* Stage 2. A
re-run on a quiescent tree would produce the receipt.

### Discriminator for the new blocker: the generator is NOT missing an arm

`hc_enc_hir_type_kind` (`hir_codec.spl:5160-5378`) has **28** `case` arms: 27
concrete ones plus the `case _` catch-all. `enum HirTypeKind`
(`src/compiler/20.hir/hir_types.spl:507`) has **27** variants. Every variant is
covered, so this is NOT a codec-completeness / generator gap — the match
DISPATCHES to the catch-all for a value that one of the 27 arms should have
matched. The next lane should treat it as a match/enum-discriminant problem in
the Stage-2 binary (nil or otherwise erased `HirTypeKind` reaching the encoder,
or a mis-tagged payload), not as "regenerate the codec", which the error message
itself misleadingly suggests.

## The `tag -1` frontier, characterised (2026-08-24, follow-up)

Four questions were asked about the new blocker. All four are now answered by
measurement, and one of the answers is a NEGATIVE that saves the next lane a
wrong turn.

### 1. There is no "tag producer". The `-1` is a hardcoded literal.

`hc_bad_tag` is called from **62** sites in `hir_codec.spl`, split exactly:

* **31 encoder catch-alls**, every one of them `case _: hc_bad_tag("X", -1)` —
  a literal, identical in all 31.
* **31 decoder sites**, every one `hc_bad_tag("X", tag)` — the real decoded tag.

So `no \`X\` arm for tag -1` means one thing only, for ANY enum `X`: **the
ENCODER's `match` fell through to its catch-all.** The `-1` carries zero
information about the offending value.

This retires the tempting reading that `HirTypeKind` and `Visibility` both
showing `-1` points at a shared discriminant producer returning `-1`. They
share nothing but the sentinel. (The already-filed
`hir_codec_visibility_bool_in_define_slot_2026-08-24.md` states this too —
"The `-1` is a hardcoded sentinel in that fallthrough, not a decoded tag" —
and it was reached here independently before that record was found.)

### 2. It is the same CLASS as the fixed `Visibility` defect, on the same path.

That record's root cause was a **bool** sitting in a `Visibility` slot: a bool
is not nil, so the codec's `if node.x == nil` guard took the ENCODE branch, and
the value then matched none of the variants. Any non-nil, wrong-typed value in
a codec'd slot produces this exact diagnostic.

Confirmed here with the same kill-switch that record used
(post-fix Stage 2 `aaac7c62…`, three-line hello world, only `SIMPLE_HIR_CACHE`
changed):

| `SIMPLE_HIR_CACHE` | rc | ending |
|---|---|---|
| `1` | 1 | `error: hir codec: no \`HirTypeKind\` arm for tag -1` |
| `0` | 1 | **error gone**; a new `[bootstrap-error-count] … point=post-store count=0` counter appears and the run advances to `error: bootstrap entry lowered to 0 MIR instructions (ret-0 stub module)` |

So the malformed value reaches only the `hir_cache_store` encode path
(`driver_hir_pipeline_lowering.spl` -> `driver_hir_cache.spl` ->
`hir_module_encode`) — the codec is the messenger, not the producer — and the
defect is **independent of the `if`-merge fix**, which concerns array element
typing and never touches this path.

### 3. NEGATIVE RESULT: `d4b1dee0d63` does NOT cover this one.

`d4b1dee0d63` ("an Option handle in `HirStmtKind.Let.type_` SIGSEGV'd
monomorphize") is the same class and an excellent candidate: a `Some(HirType)`
enum handle in a slot declared bare `HirType` would make `hc_enc_hir_type` read
the enum header as a `HirTypeKind` and fall straight through to the catch-all.

**It was already present in the tree this Stage 2 was built from.** The boot
worktree's `src/compiler/20.hir/hir_lowering/statements.spl` is byte-identical
to `origin/main` (which carries `d4b1dee0d63`), and that file did not change
during the build — the run's own before/after source snapshots differ in
exactly 3 files, all under `src/compiler/50.mir/**`. Stage 2 compiled all 750
modules from source with 0 cached.

Therefore the `HirTypeKind` fall-through has a **different producer site** from
the one `d4b1dee0d63` fixed. Do not assume that commit clears it.

### 4. Pre-existing, to the extent it can be established

The class predates this fix — the `Visibility` instance was filed AND fixed
earlier the same day, on the same encode path, with the same sentinel — and
with the cache off the post-fix binary sails past it to a later, unrelated
failure. The pre-fix Stage 2 cannot be re-run for a direct control: a parallel
session deleted that binary mid-session (only its two receipts remain at
`build/bootstrap/stage2/aarch64-apple-darwin/`). The pre/post numbers in the
section above were taken before the deletion.

### The diagnostic itself is a defect and cost real time

```
error: hir codec: no `HirTypeKind` arm for tag -1; regenerate
       src/compiler/20.hir/generated/hir_codec.spl
```

Every actionable word of this is wrong for the encoder half:

* **"for tag -1"** — no tag was decoded; `-1` is a literal.
* **"regenerate ..."** — the codec is COMPLETE (27 concrete arms vs 27
  `HirTypeKind` variants). Regenerating it changes nothing, and it sends the
  reader to the one file that is not at fault. This misdirection is what the
  count above had to be spent to refute.

The producing site is the generated encoder catch-all. A useful message would
name the SLOT being encoded and dump the offending value's runtime tag /
discriminant, and would say "a wrongly-typed value reached the encoder", not
"regenerate". Filed here rather than fixed: it needs a change to the codec
GENERATOR, not to the generated file, which is out of scope for this lane.

### Next lane's frontier

With `SIMPLE_HIR_CACHE=0`: `error: bootstrap entry lowered to 0 MIR
instructions (ret-0 stub module)`. With the cache on: find which slot hands a
non-nil, non-`HirTypeKind` value to `hc_enc_hir_type_kind` — by the `Visibility`
precedent, look for a call site passing the wrong type into a `HirType` slot.

## Admission loose end CLOSED — reproduced on an ADMITTED Stage 2 (2026-08-24)

The unadmitted-binary caveat above is discharged. A sibling lane independently
ran the sanctioned command in the boot worktree, from a **clean** tree at
`d4b1dee0d63` that carries the seed `if`-merge fix, and it minted both
receipts:

```
stage2-provenance.receipt   stage2-provenance: pure-simple
                            authority=explicit-full-bootstrap-stage2-trust-root
                            candidate_sha256=7e45db55a89aed6f04139d157467e1adb6235a3b8a1006f0dacf8221375e9b40
                            admission_receipt_sha256=1ac9c87557259e718ca9866309c614e3b53a2bd54e8a50b326e7a2c032ba2514
stage2-sanity.receipt       stage2-sanity: pass
```

Every measurement above reproduces on that admitted binary — a different build,
by a different lane, from a different tree state:

| | unadmitted `aaac7c62…` | **admitted `7e45db55…`** |
|---|---|---|
| `ands #0xfffffff8` total | 517 | **517** |
| ... inside `hc_enc_hir_module` | 0 | **0** |
| hello world, `SIMPLE_HIR_CACHE=1` | rc=1, `no \`HirTypeKind\` arm for tag -1` | **identical** |
| hello world, `SIMPLE_HIR_CACHE=0` | rc=1, `bootstrap entry lowered to 0 MIR instructions` | **identical** |

So the pre-fix `rc=139` / 7-mask result and the post-fix `rc=1` / 0-mask result
now both rest on trust-root artifacts, and the `tag -1` characterisation holds
on an admitted Stage 2. The earlier admission failure is confirmed to have been
purely the concurrent-edit artifact described above, not a property of the fix.

Still true, and still the honest bound: **the SIGSEGV this record documents is
eliminated; Stage 2 does not yet compile a hello world.**
