# SimpleOS aarch64 freestanding: `rt_slice` mis-decodes RAW indices that are multiples of 8

Date: 2026-08-31
Lane: aarch64 in-guest toolchain components (EDK2/AAVMF pflash -> BOOTAA64.EFI)
Gate: `scripts/check/check-simpleos-aarch64-components-in-guest-efi.shs`
File: `examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c`
Compiler: the RUST SEED (`src/compiler_rust/target/release/simple`, freshly built).

## Not the riscv64 `rt_value_int` identity bug

The riscv64 defect (PR #189, still OPEN at the time of writing) is that
`rt_value_int` was an identity function while `rt_index_get` opens
`if (!IS_INT(index)) return NIL_VALUE;`. **Neither x86_64 nor aarch64 has that
defect**, measured at `origin/main` ee6942c11534:

| arch | `rt_value_int` | verdict |
|---|---|---|
| riscv64 | `baremetal_runtime_core.inc.c:956` `return value;` | IDENTITY — defective (PR #189, OPEN) |
| x86_64  | `rt_extras.c:112` `return ENCODE_INT(i);` (strong; the weak `auto_stubs.c:3633` nil stub is overridden) | CORRECT |
| aarch64 | `freestanding_runtime.c:1463` `return value << 3;` with `RT_VALUE_TAG_INT == 0x0` (`:50`) | CORRECT |

## The actual aarch64 defect

There are **two distinct index ABIs** in the canonical hosted runtime
`src/runtime/runtime_native.c`, and they are not interchangeable:

* **TAGGED** — `rt_index_get` (`:8554`) and `rt_index_set` (`:8569`) both open
  `if ((idx & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_INT) return nil;` then `idx >> 3`.
* **RAW** — `rt_slice` (`:3816`) uses `start` / `end` / `step` verbatim, with no
  decode at all. So do `rt_array_get` (`:7033`, whose comment states it:
  *"Native array ABI matches the Rust runtime: indices are raw i64 values"*),
  `rt_tuple_get` (`:7862`), `rt_bytes_u8_at` (`:7636`), `rt_array_repeat`
  (`:7292`) and `rt_string_char_at` (`:3010`).

The aarch64 freestanding runtime routes **both** classes through one heuristic,
`rt_index_arg` (`:225`):

    static spl_i64 rt_index_arg(spl_i64 value) {
        if ((((spl_u64)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_INT) {
            return value >> 3;
        }
        return value;
    }

Because `RT_VALUE_TAG_INT` is `0x0`, this test **cannot distinguish a tagged int
from a raw int whose low three bits happen to be zero.** Every raw index that is
a multiple of 8 is silently divided by 8. For a strictly-tagged callee this is
harmless (raw values never arrive). For `rt_slice`, whose arguments are raw by
contract, it is a live corruption.

The x86_64 sibling gets this right and says so in the code
(`arch/x86_64/boot/rt_extras.c:1241`):

    static int64_t _rv_to_index(RuntimeValue v) {
        /* Cranelift bare-metal slice lowering passes raw indices, not boxed ints. */
        return (int64_t)v;
    }

Compiler-side confirmation: `substring` lowers to `rt_slice(text, start, end, 1)`
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs:1324-1360`),
the one-bound form taking `end` from `rt_len`, and `step` is a bare
`MirInst::ConstInt { value: 1 }` — raw, not tagged.

## Why this reproduces "first key empty, second key correct" exactly

Defect 1 of `simpleos_aarch64_in_guest_text_defects_not_len_abi_2026-08-31.md`:

    [caret] built message: {"role":"user","content":"CARET_RTT_CONTENT"}
    [caret] extracted role=
    [caret] extracted content=CARET_RTT_CONTENT

`extract_json_string` (`src/app/llm_caret/json_helpers.spl:152`) first calls
`json_find` (`:128`), which scans with `s.substring(i, i + nlen)`.

For key `role`: needle `"role":` has `nlen = 7` and matches at `i = 1`. That
probe is `substring(1, 8)`. `start = 1` -> `1 & 7 == 1`, passed through
correctly. **`end = 8` -> `8 & 7 == 0`, read as tagged, returned as `8 >> 3 = 1`.**
Now `end (1) < start (1)` is false but `end == start`, so `rt_slice` returns the
EMPTY string, which never equals the needle. The single position at which the
key matches is the one position the scan cannot see, so `json_find` returns -1
and `extract_json_string` returns `""`.

For key `content`: needle `"content":` has `nlen = 10` and matches at `i = 15`.
The probe is `substring(15, 25)`; `15 & 7 == 7` and `25 & 7 == 1`, so neither
bound is a multiple of 8, both survive, the match is found, and the value is
extracted correctly.

That is the whole of the reported symptom — a positional defect on the same
input in the same call sequence — derived from the arithmetic, not inferred by
analogy. It also explains why the `.len()` u32/i64 ABI fix (PR #173) changed the
serial output not at all: the length was never wrong.

## Fix

`rt_slice` takes its three index arguments RAW, matching
`runtime_native.c:3816` and `arch/x86_64/boot/rt_extras.c:1246`.

## Deliberately NOT changed in this pass

`rt_array_get` (`:649`), `rt_tuple_get` (`:883`), `rt_tuple_set` (`:892`),
`rt_bytes_slice` (`:1352`), `rt_bytes_u8_at` (`:1379`) and `rt_array_repeat`
(`:852`) are RAW-ABI in the hosted twin yet also route through `rt_index_arg`,
so they carry the same latent multiple-of-8 corruption. They are left alone here
because (a) no in-guest evidence yet implicates them, and (b) two internal
callers inside this same file — `:1191` and `:1230` — invoke
`rt_array_get(collection, rt_int(i))` with a TAGGED index, so flipping
`rt_array_get` to raw requires fixing those call sites in the same change.
Doing that without evidence risks trading a known defect for an unknown one.

`rt_index_get` (`:721`) and `rt_index_set` (`:756`) are TAGGED-ABI and must keep
decoding; leaving `rt_index_arg` there is correct-by-accident rather than
correct-by-construction, but it is not a defect.

## Verified in-guest (EDK2/AAVMF pflash -> BOOTAA64.EFI, no `-kernel`, no isa-debug-exit)

Kernels rebuilt from scratch (`rm -rf build/os/aarch64_components`) with the
RUST SEED, all four rows.

BEFORE:

    FAIL — 4 component(s) evaluated in-guest on SimpleOS aarch64 under EDK2/AAVMF
    pflash -> BOOTAA64.EFI (no -kernel, no isa-debug-exit), 1 completed a real
    round-trip; offenders: caret(ran but round-trip incomplete; last own line:
    [caret] FAIL role did not round-trip) testrun(... [testrun] FAIL parser did
    not report failed=1) mcp(link: undefined symbol: rt_closure_func_ptr
    undefined symbol: rt_closure_new )

AFTER:

    FAIL — 4 component(s) evaluated in-guest on SimpleOS aarch64 under EDK2/AAVMF
    pflash -> BOOTAA64.EFI (no -kernel, no isa-debug-exit), 2 completed a real
    round-trip; offenders: testrun(ran but round-trip incomplete; last own line:
    [testrun] FAIL parser did not report failed=1) mcp(link: undefined symbol:
    rt_closure_func_ptr undefined symbol: rt_closure_new )

The caret serial transcript, the defect's primary evidence, flipped exactly as
the arithmetic predicted — `role` now extracts:

    [caret] built message: {"role":"user","content":"CARET_RTT_CONTENT"}
    [caret] extracted role=user
    [caret] extracted content=CARET_RTT_CONTENT
    [caret] redacted: key [REDACTED:aws_access_key_id:MPLE] trails CARET_KEEPME

devtool stayed green. **Defect 1 of
`simpleos_aarch64_in_guest_text_defects_not_len_abi_2026-08-31.md` is FIXED.**

## Defect 2 (`parse_test_output`) is NOT this bug — it is arch-independent

The testrun row is byte-identically red before and after this fix, and it is
byte-identically red on **x86_64**, whose `rt_slice` was already correct
(`rt_extras.c:1241` `_rv_to_index` is the identity). Both arches print:

    [testrun] feeding a 3-example spec transcript to the real parser
    [testrun] FAIL parser did not report passed=2
    [testrun] FAIL parser did not report failed=1

Two freestanding runtimes with *different* and independently-correct slice ABIs
failing identically means the defect is not in either runtime's index handling.
It needs its own investigation, upstream of the arch layer.
