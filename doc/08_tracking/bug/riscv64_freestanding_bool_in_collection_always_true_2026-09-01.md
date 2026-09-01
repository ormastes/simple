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
