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
