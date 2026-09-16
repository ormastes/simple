# riscv64 freestanding: a `bool` read out of a tuple or array is ALWAYS `true`

- Status: **OPEN** — root cause of goal item 1 row 2 (SimpleOS riscv64 in-guest
  build-and-run sanity). Not fixed.
- Date: 2026-09-01
- Lane: `scripts/check/check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`,
  row 2 (`buildrun`)
- Measured under real OpenSBI v1.4 `-bios fw_payload`, positively-asserted
  embed, no `-kernel`, no `isa-debug-exit`.

## Symptom, at the top

Row 2 boots ONCE (the OpenSBI banner appears exactly one time — the machine
never resets), reaches its three `[buildrun]` rungs, and then the GUEST
re-enters `spl_start` repeatedly (67 times in one boot) until the bump arena is
gone. Serial now names it, after the fix in the sibling change:

```
[rv64] FATAL bump heap exhausted (low half) - rv_alloc returned NULL
```

That is a SYMPTOM. The allocation is unbounded because the parser is in an
infinite loop.

## Root cause, measured

`false` read back out of a tuple or an array in the freestanding riscv64 build
evaluates as `true`. In-guest probe results, one boot:

| expression | expected | measured |
|---|---|---|
| plain `bool` return of `false` | false | **false (correct)** |
| `val (m, v) = f()` where `f` returned `(false, 0)` | m = false | **true** |
| same tuple's `i64` element | 0 | 0 (correct) |
| `(0, false)` — bool in position 1 | false | **true** |
| `(false, true)` — both positions | false, true | **true, true** |
| `var ab: [bool] = [false, true]; ab[0]` | false | **true** |

So it is not tuple-specific and not position-specific: **any `bool` that
round-trips through a heap collection reads as `true`.** An unboxed `bool`
return is fine, which is why almost nothing else on this lane trips it.

`.len()` is INNOCENT and was ruled out by direct measurement in the same boot —
on `[i64]`, `empty.len() == 0`, `empty.len() > 0`, `twelve.len() == 12`,
`> 10`, `> 11`, `> 12` and the `while i < len` tick all answer correctly. The
`.len()` fail-open of
`riscv64_freestanding_len_eq_zero_guard_never_fires_2026-09-01.md` does not
reproduce on plain arrays and is a different defect.

## How it hangs the parser

`fn f(a):\n    a\n` — a function whose body is a **bare identifier statement** —
never finishes parsing. `parse_statement()`
(`src/compiler/10.frontend/core/parser_stmts.spl:1009`) routes an identifier-led
statement through:

```simple
if kind == TOK_IDENT:
    val (bc_matched, bc_call) = try_parse_bare_ident_string_call()
    expression = if bc_matched: bc_call else: parse_expr()
```

`try_parse_bare_ident_string_call()` (:228) correctly takes its
`return (false, 0)` early-exit — verified in-guest, the rollback probes fire —
but the destructured `bc_matched` reads **true** at the call site. Measured over
one boot: `bc-matched` 170,313 times, `bc-nomatch` **zero**. So `parse_expr()`
is never called, no token is consumed, and `parse_block()`'s `while true:`
(parser_stmts.spl:322) spins, allocating per iteration.

A literal body (`1`, `1 + 2`) takes the `else` branch and never destructures a
tuple — which is exactly the discriminator the bisect measured.

## The bisect that isolated it

Every variant below was parsed in-guest, in one boot each, appending until the
boot died. All PASSED: `fn main(): print "x"`, `fn f(a): print "x"`,
`fn f(a: i64): print "x"`, `fn f(a: i64, b: i64): print "x"`,
`fn f() -> i64: print "x"`, `fn f(a: i64) -> i64: print "x"`, `fn f(): 1`,
`fn f(): 1 + 2`, `fn f() -> i64: 1`. Only `fn f(a): a` and
`fn f(a: i64) -> i64: a` hang. Type annotations, return types, parameter count
and arithmetic are all innocent.

With row 2's program reduced to `fn main():\n    print "..."\n`, the WHOLE row
runs green in-guest — frontend, `MirLowering.lower_module`, and
`interpret_hir_module` — printing its nonce-carrying output and
`[buildrun] build-and-run row exited rc=0`, using under 16 MiB. **In-guest MIR
lowering and interpretation are not the problem.** Only the parser's
bare-identifier path is.

## Where the fix belongs — a lead, not a conclusion

The Simple boolean is a TAGGED `RuntimeValue` in generated code: the seed states
`true = 11, false = 19`
(`src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:2628`). Tagged
`false` is **19, not 0**. A consumer that uses a collection element directly as
a machine truth value therefore sees 19 and reads `true`. That fits every row of
the table above and fits `plain bool return` being correct (never boxed).

Two things are NOT yet established and must not be written up as fact:
- which code emits the un-decoded read (no runtime unbox symbol is even called —
  `nm kernel.elf` shows `rt_len`, `rt_array_len`, `rt_dict_len`, `rt_dict_get`
  and `rt_value_truthy` are **absent from the linked image**, so the element
  read is inline codegen, not a runtime call);
- whether this is riscv64-specific or general to this backend.

Note separately that `examples/09_embedded/simple_os/arch/common/baremetal_runtime.h`
defines `TRUE_VALUE ENCODE_INT(1)` (= 8) and `FALSE_VALUE ENCODE_INT(0)` (= 0),
which disagrees with the codegen's 11/19. Any C code comparing against those
macros is wrong. That is a real second defect; it is not proven to be this one.

## Reproduce

Host is blocked: `native-build` of a minimal reproducer fails first with an
unrelated, pre-existing `semantic: method 'len' not found on type 'enum'
(receiver value: Option::None)`, under both `--backend cranelift` and
`--entry-closure`. The interpreter (`simple run`) is CORRECT on the same file,
so the reproducer needs a compiled backend.

In-guest, add to
`examples/09_embedded/simple_os/arch/riscv64/buildrun_sanity_entry.spl`:

```simple
fn tup_early_false(flag: bool) -> (bool, i64):
    if not flag:
        return (false, 0)
    (true, 77)
```

destructure `tup_early_false(false)` and print the bool. Cycle cost: entry-only
`native-build` ~60s warm, fw_payload rebuild + boot ~4 min.

## Next step

Find the codegen site that materialises a `bool`-typed element read from
`rt_tuple_get` / `rt_array_get` and use it as a condition without decoding the
tagged `19`. Fix there, not in the parser: forcing `parse_block` to advance
would mask a defect class that reaches every `bool` in every collection.

---

# FIFTH SESSION MEASUREMENT (2026-09-01) — host native-build is GREEN, and codegen uses TWO bool representations

## The host block recorded above was the reproducer's shape, not a real block

The previous session recorded "Host is blocked: `native-build` of a minimal
reproducer fails first with an unrelated, pre-existing `semantic: method 'len'
not found on type 'enum'`". That was a property of *that* reproducer, not of the
host lane. A reproducer with no `Option`/`.len()` surface native-builds cleanly
on host x86_64 (`rc=0`, ~29s) and **runs CORRECTLY**:

```
GOOD m=false
GOOD ab0=false
0
```

covering both shapes from the table above — a `bool` destructured out of a
returned tuple, and `ab[0]` out of a `[bool]` array literal. So the defect is
**NOT general to the compiled backend**. It is specific to the riscv64
freestanding lane. This narrows the search and contradicts nothing previously
measured.

## What the host disassembly shows: tuples and arrays disagree, deliberately

Disassembling the working host binary shows codegen uses **two different and
mutually incompatible `bool` representations**, one per container kind, each
internally consistent:

**Tuple path — RAW 0/1, consumed by a bit-0 test.** `tup_early_false` inlines
the tuple construction and stores raw words:

```
2d27:  mov  $0x10,%edi ; call rt_alloc
2d31:  movq $0x1,(%rax)        <- `true`  stored as RAW 1
2d38:  movq $0x4d,0x8(%rax)
...
2d4c:  xorps %xmm0,%xmm0
2d4f:  movups %xmm0,(%rax)     <- `false` stored as RAW 0 (both words)
```

and the consumer at the destructure site tests bit 0 of the word directly:

```
2c63:  testb $0x1,(%rdx)       <- RAW bit-0 test, no tag decode
```

**Array path — TAGGED 11/19, consumed by an equality test against 11.** The
`[false, true]` literal pushes tagged constants through the runtime:

```
2c97:  mov $0x13,%esi ; call rt_array_push   <- 0x13 = 19 = TAGGED false
2ca4:  mov $0xb,%esi  ; call rt_array_push   <- 0x0b = 11 = TAGGED true
2cc8:  call rt_array_get
2ccd:  cmp $0xb,%rax                         <- compares against TAGGED true
```

## Why this is the mechanism, and what it predicts

The two schemes are only safe while producer and consumer agree. **Tagged
`false` is 19, whose bit 0 is SET.** So the instant a TAGGED bool reaches the
tuple consumer's `testb $0x1`, it reads `true` — and so does tagged `true` (11,
bit 0 also set). That is precisely an "always true" bool, for both operands,
which is exactly the measured table. The i64 element of the same tuple reading
back correctly is also explained: only the bool word is misencoded, the pointer
and the integer slot are fine.

So the freestanding lane is **mixing the two conventions** — writing a tagged
bool into a slot whose reader uses the raw bit-0 test (or the mirror-image
mismatch on the array path, where a non-11 value reads false). The host is green
only because there each container's producer and consumer happen to match.

This supersedes the earlier "a consumer uses the collection element directly as
a machine truth value" lead only in precision, not in direction: that lead was
right, and the host disassembly now names both conventions and the exact
instruction (`testb $0x1`) that cannot survive a tagged operand.

## Status of the next step

Still open: WHICH side diverges in the freestanding build (a baremetal
`rt_array_*` / tuple store that re-encodes, versus codegen emitting a tagged
constant where the host emitted a raw one). Not yet established; must not be
written up as fact until a freestanding build is disassembled or instrumented.

## Reproducer, host, cheap

`/mnt/data/tmp/rv64x/repro.spl` in this session; the shape is the
`tup_early_false` function quoted above plus `var ab: [bool] = [false, true]`.
Interpreter and host `native-build` both GREEN — so any guard built on it must
run the freestanding lane, or a freestanding-flagged host build, to be RED.

---

# ROOT CAUSE, MEASURED AND FIXED (2026-09-01, fifth session)

## It is the Cranelift boxed-closure boundary, not the parser and not the C runtime

The riscv64 lane builds with **`--backend cranelift --entry-closure`**
(`scripts/os/build-simpleos-riscv64-interpreter-kernel.shs:113-120`). That
matters: the LLVM backend, which the host uses by default, is CORRECT here, and
the two backends do not share this code.

Disassembling the real row-2 kernel at the exact call site this record already
identified (`parse_statement` -> `try_parse_bare_ident_string_call`) shows the
destructure lowering verbatim:

```
803216d4:  jalr  ... <...try_parse_bare_ident_string_call>
803216dc:  li    a1,0
803216f4:  jalr  a2          ; -> rt_tuple_get(tuple, 0)
8032170c:  jalr  a1          ; -> rt_value_unbox_int(element)
80321710:  mv    s6,a0
...
80321754:  zext.b a0,s7
80321758:  bnez   a0,...     ; branch on the "decoded" bool
```

(The two indirect targets were resolved from their in-image pointer words to
`rt_tuple_get` at `0x80201330` and `rt_value_unbox_int` at `0x80203230`.)

The source of that sequence is the `TypeId::BOOL` arm of the boxed-closure
unbox, present in two places documented in-tree as exact mirrors —
`codegen/closure_boxed_entry.rs` (`unbox_arg`) and
`codegen/instr/closures_structs.rs` (`unbox_from_closure_boundary`):

```rust
TypeId::BOOL => {
    let raw = call_runtime_1(ctx, builder, "rt_value_unbox_int", tagged);
    builder.ins().icmp_imm(IntCC::NotEqual, raw, 0)
}
```

**`rt_value_unbox_int` is bit-preserving for anything that is not `TAG_INT`,
and a tagged BOOL is `TAG_SPECIAL` — so here it is a PASSTHROUGH, not a
decode.** The `!= 0` that follows therefore answers TRUE for `true` (11) *and*
for `false` (19), because both are non-zero. The matching `box_result` emits
exactly those tagged values via `rt_value_bool`, so the round trip was
self-defeating: box `false` -> 19 -> unbox -> `19 != 0` -> `true`.

This explains every row of the symptom table, including the two that previously
looked inconsistent:
- the tuple's `i64` element reads correctly, because the `I64` arm's
  `rt_value_unbox_int` *is* the right decode for a tagged int;
- a plain `bool` return is correct, because it never crosses the boxed boundary.

## Two earlier hypotheses in this record are REFUTED, not merely superseded

- **The `.len()` fail-open** was already ruled out by the previous session; it
  stays ruled out and is a separate defect.
- **The branch terminator** (`codegen/instr/body.rs:1300`,
  `icmp_imm(IntCC::NotEqual, cond_val, 0)`) was this session's first hypothesis
  and is **wrong for this defect**. The disassembly settles it: the branch
  operand is already `I8` (`zext.b` + `bnez`), so that `cond_ty != I8` path is
  never taken here. A change there was written, measured against the
  disassembly, and REVERTED rather than shipped. Recorded so the next session
  does not re-derive it. (Whether a wide tagged value can reach that terminator
  by some other route was not established either way, and no claim is made.)
- The `TRUE_VALUE`=8 / `FALSE_VALUE`=0 macro disagreement is real but is NOT
  this defect; it is filed separately as
  `baremetal_bool_macros_disagree_with_codegen_tags_2026-09-01.md`.

## The fix

Both mirror sites now decode the TAGGED value directly, using the same falsy set
the LLVM backend already uses in `runtime_int_truthy_i1`:

    falsy = (v == 0) | (v == 19 /* tagged false */) | (v == 3 /* nil */)

This is also correct for a RAW 0/1 bool (0 is falsy, 1 is not), so it is safe
whichever representation the producer used.

## Why the guard is a source-shape ratchet

Stated plainly rather than papered over: `scripts/check/check-cranelift-boxed-bool-decode.shs`
checks the SHAPE of the two definitions, not runtime behaviour. A behavioural
host test was attempted and is genuinely blocked — three reproducer shapes
(positional file, closure value, and the lane's own `--source`/`--entry` form)
either inlined the call away (zero `rt_value_unbox_int` or boxed-thunk symbols
in the artifact) or died first on an unrelated pre-existing stdlib error
(`nil is forbidden by the non-optional return contract of 'file_hash_sha256'`),
which is the same wall the previous session hit. The behavioural test is the
in-guest lane itself. The guard is RED against this fix's own parent
(`633641ee097`, naming both sites) and GREEN after, with a fatal 5-fixture
`--selftest`.

## Correction to this record's own earlier text

The host is NOT generally blocked, and the host backend is NOT affected: a
reproducer with no `Option`/`.len()` surface native-builds and runs correctly on
host x86_64. The host lane's correctness is a property of the LLVM backend, not
evidence that the defect was absent.

## The passthrough claim, verified against the DEFINITION THAT WINS THE LINK

Two in-tree comments assert the opposite of the premise above — that
`rt_value_unbox_int` already decodes tagged bools
(`codegen/instr/mod.rs:1598`: "wide box -> value, TAG_INT -> >>3, **tagged
true/false -> 1/0**, everything else verbatim"; similarly
`cranelift_emitter.rs:800`). Taken at face value they would make this fix a
no-op on a non-bug, so they were checked rather than believed — this is exactly
the duplicate-definition trap, and a tree-wide grep or a source comment cannot
settle it.

Disassembled out of the actual row-2 `kernel.elf`, `rt_value_unbox_int`
(`0x80203230`) is a thin wrapper that tail-calls `simpleos_raw_or_encoded_int`
(`0x80202538`), whose entire body is:

```
    lbu   a0,-24(s0)      ; low byte of v
    andi  a0,a0,7         ; tag bits
    bnez  a0,<passthrough>
    ld    a0,-24(s0)
    srai  a0,a0,0x3       ; TAG_INT  -> v >> 3
    j     <ret>
<passthrough>:
    ld    a0,-24(s0)      ; everything else -> v, VERBATIM
```

i.e. `(v & 7) == 0 ? v >> 3 : v`. **There is no bool case at all.** Tagged
`false` is 19, `19 & 7 == 3`, so it takes the passthrough arm and returns 19;
`19 != 0` is true. The premise is confirmed against the linked definition.

So those two comments describe the HOST runtime's `rt_value_unbox_int`, not the
baremetal one that this lane actually links. That divergence is itself worth
noting: the baremetal implementation missing the bool arm is a second way to
express the same defect, and is captured in
`baremetal_bool_macros_disagree_with_codegen_tags_2026-09-01.md`.

The fix as applied does not depend on which runtime is linked — it decodes the
tagged value in codegen rather than delegating to `rt_value_unbox_int` — which
is why it was preferred over adding a bool arm to the C.

---

# CORRECTION — the section above named the WRONG SITE. Read this one.

The "ROOT CAUSE, MEASURED AND FIXED" section above correctly identified the
MECHANISM (a tagged `false` = 19 surviving undecoded into a non-zero test) but
attributed it to the Cranelift boxed-closure unbox arm
(`closure_boxed_entry.rs` / `instr/closures_structs.rs`). **That attribution is
wrong and the change based on it has been reverted** (`ea7df60f08b`). It is left
in this record rather than deleted, because the way it was caught is the point.

## How it was caught

The rule the task set — *before concluding anything, verify with `nm`/objdump
that your change is actually IN the image* — is what caught it. The kernel was
rebuilt with the Cranelift change and the call site re-disassembled. It was
**byte-identical** to the pre-fix kernel: still

```
jalr <try_parse_bare_ident_string_call>
li   a1,0 ; jalr -> rt_tuple_get(tuple, 0)
          ; jalr -> rt_value_unbox_int          <- STILL a call, not inline
mv   s6,a0 ; zext.b a0,s7 ; bnez
```

with the second target still resolving to `rt_value_unbox_int`. Had the
Cranelift arm been the live site, that call would have disappeared entirely and
been replaced by inline tag compares. It was not. The change fixed nothing, and
would have shipped as a false fix with a guard pinning it.

## The actual root cause

The live path is the MIR `UnboxInt` lowering, which calls `rt_value_unbox_int` —
and **there are TWO definitions of that function for freestanding riscv64**:

| definition | tagged-bool arm |
|---|---|
| `arch/common/boot/freestanding_value_registry_impl.h:112` | **present** (`if (value == 11) return 1; if (value == 19) return 0;`) |
| `arch/riscv64/boot/baremetal_runtime_core.inc.c:1093` | **ABSENT** |

The defective one is the one the image links, proven by disassembly: the
kernel's `rt_value_unbox_int` tail-calls `simpleos_raw_or_encoded_int`, whose
entire body is `(v & 7) == 0 ? v >> 3 : v`. Tagged `false` is 19, `19 & 7 == 3`,
so it took the passthrough arm and returned 19; `19 != 0` is true, and so is 11.

**This is exactly the duplicate-definition trap the task warned about, in a form
nobody had checked**: the warning named `baremetal_stubs.c` vs
`baremetal_runtime_core.inc.c`, and the real pair here is
`baremetal_runtime_core.inc.c` vs `freestanding_value_registry_impl.h`. A
tree-wide grep for `value == 19` finds the GOOD sibling and reports success
while the image links the bad one — which is very likely why this defect
survived several investigations.

## The fix

Give the linked definition the missing arm (`71222183a0a`), restoring the
contract that the canonical hosted runtime
(`src/compiler_rust/runtime/src/value/sffi/value_ops.rs:80-87`), the codegen
comments (`codegen/instr/mod.rs:1598`) and the sibling freestanding
implementation all already state. `TAGGED_BOOL_TRUE`/`TAGGED_BOOL_FALSE` were
added to `baremetal_runtime.h`; the pre-existing `TRUE_VALUE`/`FALSE_VALUE` were
deliberately left alone so their separately-tracked disagreement with codegen
does not change as a side effect of this fix.

Guard: `scripts/check/check-baremetal-tagged-bool-decode.shs` — judges each
definition body separately, so a good sibling cannot excuse a bad one. RED
before the fix (naming `baremetal_runtime_core.inc.c:1093`), GREEN after, fatal
6-fixture `--selftest` including the duplicate-definition case itself.

---

# VERIFIED IN-GUEST (2026-09-01) — the parser hang is FIXED; row 2 now fails further downstream

Full gate run under real OpenSBI v1.4 `-bios fw_payload`, nonce
`631998c976589a0e`, gate selftest OK (23 fixtures), rows checked = 2.
Row 1 (interpreter) PASSES. Row 2 still FAILS, but for a **different reason**.

| measurement | before this fix | after |
|---|---|---|
| OpenSBI banners (machine resets) | 1 | 1 |
| `[buildrun]` guest re-entries | **67** | **1** |
| `[rv64] FATAL bump heap exhausted` | present | **0** |
| `[buildrun] phase=hir-ok` | never reached | reached |
| `[buildrun] phase=mir-ok functions lowered` | never reached | reached |
| terminal state | reboot-loop until arena gone | `FAIL run error: module has no main function` |

The unbounded allocation, the guest restart loop and the arena exhaustion are
**gone**. The parser terminates. `parse_and_build_module` completes, HIR is
built, MIR lowering runs, and control reaches the run stage. That is the whole
of the defect this record tracks, and it is fixed.

## Status of this record

**FIXED** for the tagged-bool defect. Row 2 as a whole is **still RED**, so goal
item 1 row 2 is not green — the honest statement is that this defect is closed
and the next one is now the blocker, not that the row is done.

## What blocks row 2 now — it is the OTHER open record, not a regression

`[buildrun] FAIL run error: module has no main function` is verbatim the
downstream symptom already described in
`riscv64_freestanding_len_eq_zero_guard_never_fires_2026-09-01.md`, which states
that the `hir.functions.len() == 0` fail-open "let a functionless module through
to `interpret_hir_module`, which then reported 'module has no main function' — a
correct but far downstream symptom that cost two sessions of investigation aimed
at the wrong phase."

So the two records are now in sequence rather than in competition: the tagged
bool was hiding the `.len()` defect behind an infinite loop, and fixing it has
exposed the `.len()` defect as the next blocker. Note that the `.len()` record's
own measurements ruled `.len()` innocent on plain arrays, so the remaining
question — whether the module genuinely has no functions, or has them and the
guard/lookup misreads — is NOT yet settled and must be measured, not assumed.

## Next step

Probe, in-guest, the actual function count of the built HIR module immediately
before `interpret_hir_module`, and print the raw value rather than a comparison
result. Do not assume the module is empty: `phase=mir-ok functions lowered`
printed, which is weak evidence that lowering saw something.
