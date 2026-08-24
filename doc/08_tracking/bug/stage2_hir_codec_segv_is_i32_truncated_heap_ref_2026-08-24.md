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
