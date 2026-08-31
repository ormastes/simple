# Freestanding `text.len()` was garbage: RuntimeString.len declared uint32_t, codegen loads i64 (2026-08-31)

Status: FIXED (root cause + gate). In-guest re-run of the riscv64 components
lane is NOT yet done — see "What is still open".

Supersedes the `text.len()` half (defect 1) of
`doc/08_tracking/bug/riscv64_freestanding_runtime_text_len_and_loop_concat_2026-08-31.md`.
That record's own hypothesis — that `rt_len` returns a raw integer where the
call site expects an `ENCODE_INT` tagged value — is **wrong**, and its warning
not to blanket-encode `rt_len`'s return was correct for the wrong reason:
`rt_len` is never called at all.

## It is genuinely wrong, not bytes-vs-chars

The subject in the probe transcript is `{"role":"user"}` — pure ASCII, so bytes
and characters coincide and the separate
`text_len_substring_bytes_but_index_chars_2026-08-30.md` contract question
cannot explain anything here. The value returned in-guest is not 15-in-another-
unit; it is **8030518997231337487**.

## Root cause

`.len()` does not lower to a call. `compile_inline_len`
(`src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs`, reached from
both `rt_len` redirect sites) expands it inline to:

* load the object-type byte at offset 0,
* GEP to **offset 8** and **`build_load(i64_type, ...)`**.

The compiler emits string objects whose payload starts at **offset 16**, and the
hosted runtime agrees exactly — `RtCoreString` is
`{ u32 kind; u32 reserved; u64 len; char data[]; }`
(`src/runtime/runtime_native.c:1011`).

The riscv64 baremetal runtime declared:

```c
typedef struct { HeapHeader hdr; uint32_t len; char data[]; } RuntimeString;
```

`len` is 32 bits at offset 8, `data` at offset 12. Every C accessor in that file
reads `s->len` as the u32 and is therefore **self-consistent** — which is
precisely why `substring`, equality, `trim`, `starts_with`, `chars()` and the
bounded scan all probed EXPECTED in-guest and only `.len()` was wrong.

The codegen-inlined i64 load at offset 8 picks up the u32 length in its low half
and the **first four payload bytes** in its high half:

```
0x6F72227B_0000000F = 8030518997231337487
       ^^^^^^^^ "{\"ro", little-endian     ^^ 15, the real byte length
```

Reproduced numerically by the selfcheck below, which prints exactly that value.

That is the stall. `json_find` (`src/app/llm_caret/json_helpers.spl:128`) loops
`while i <= slen - nlen`; `parse_test_output` scans its transcript the same way.
With `slen` ≈ 8.0e18 the bound is unreachable, so both modules emit their real
product output and then scan forever with no trap — the exact reported symptom,
on two independent modules.

## Not new: the same defect was fixed on x86_64 and then reverted

`doc/08_tracking/bug/x64_rt_extras_runtime_string_layout_mismatch.md` is the
same defect, root-caused to the same field on 2026-07-12, in the SHARED header
`examples/09_embedded/simple_os/arch/common/baremetal_runtime.h`, and fixed to
`uint64_t` with `_Static_assert`s. Both the `uint64_t` and the asserts are
**absent from that header at `origin/main` today** — the tree wipe
`6f86ff32a7d` / restore `ae55a746719` reverted them. Only the local copy in
`arch/x86_64/boot/baremetal_stubs.c` survived, and it still carries the comment
`/* MUST be uint64_t to match compiler-emitted objects */`. The riscv64 and
arm64 lanes were never fixed in the first place.

## Fix

`uint32_t len` → `uint64_t len`, plus `_Static_assert(offsetof(len)==8)` and
`_Static_assert(offsetof(data)==16)` so the contract cannot be silently reverted
again, in:

- `examples/09_embedded/simple_os/arch/common/baremetal_runtime.h` (restores the 2026-07-12 fix)
- `examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c` (the file the components lane links)
- `examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_stubs.c`
- `examples/09_embedded/simple_os/arch/riscv64/boot/ghdl_boot_info_runtime.c`
- `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c`

The `.len()` = BYTES contract is untouched: this is a field-width fix, not a
change of unit. The selfcheck asserts a 5-byte / 3-character UTF-8 string still
reports 5.

Every allocation site in the riscv64 core uses `sizeof(RuntimeString)`
symbolically (audited: no hardcoded `12`), so payload placement heals with the
struct.

## Gate

`scripts/check/check-freestanding-string-len-abi.shs` + selfcheck
`src/runtime/test/rt_freestanding_string_len_abi_selfcheck.c`. Host-compiled, no
OS boot, no cross toolchain, seconds. Two fail-closed checks: the selfcheck
reproduces the defect against the 32-bit layout (exit 2 "vacuous" if it cannot)
then asserts the 64-bit layout meets the codegen contract; and every 64-bit
freestanding `RuntimeString` must declare a 64-bit `len`.

Measured, on the real product files:

```
# pre-fix (the five files stashed back to origin content)
FAIL — 8 check(s) run, 5 failed: .../baremetal_runtime.h(RuntimeString.len is uint32_t, must be uint64_t) ... (5 lanes named)

# post-fix
reproduced: codegen .len() over the 32-bit-len layout = 8030518997231337487 (expected 15) -- an unbounded `while i < s.len()`
rt_freestanding_string_len_abi_selfcheck: OK
PASS — 8 check(s) run, codegen .len() ABI (i64 len at +8, data at +16) holds on every 64-bit freestanding lane
```

## Deliberately NOT changed

- **32-bit lanes** (`riscv32`, `arm32`, `x86_32` `baremetal_stubs.c`,
  `riscv32/minimal_shims.c`): their runtime word is 32 bits and there is no
  measurement showing their layout is wrong. Widening on an assumption would be
  the mirror of this bug.
- `examples/09_embedded/simple_os/arch/common/baremetal_min_stdout.h` declares
  its own `BaremetalRuntimeString` with a `uint32_t len` (fallback branch, used
  only when `baremetal_runtime.h` is absent). It is included by the shared
  RV32/RV64 16550 stdout capsule, **not** by the components lane, so it is out of
  scope here — but it is the same latent shape on the 64-bit side of that shared
  capsule and should be measured.
- `RuntimeArray` in the common header (`uint32_t len`/inline items) diverges from
  the riscv64 core's `RuntimeArray` (`uint64_t len`/pointer). The 2026-07-12
  record flagged this and scoped it out; it is still open and still unmeasured.
- **Defect 2** of the riscv64 record (in-loop string accumulation producing a
  single character, and the SUSPECT string-builder tranche) is untouched. It may
  or may not fall out of this fix; re-probe before diagnosing it further.

## What is still open

The riscv64 components lane could not be re-run from this worktree: the probe
and component entries (`text_primitive_probe_entry.spl`,
`{caret,testrunner,devtool}_component_entry.spl`) exist only as uncommitted work
in another lane's worktree and are in neither this tree nor `origin/main`. The
fix therefore rests on the primary-source chain above (codegen's i64 load at +8,
the hosted layout, the reproduced 8030518997231337487) and the gate — **not** on
a fresh in-guest transcript. Re-running caret and the test runner in-guest is the
outstanding confirmation.
