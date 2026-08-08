# BUG: freestanding native-build miscompiles a u64 range comparison across a function boundary

**Status:** open
**Severity:** high (silently wrong arithmetic in freestanding/baremetal code)
**Component:** compiler / freestanding native-build (`clang --target=x86_64-unknown-elf` path)
**Found:** 2026-07-08, SimpleOS x86_64 ring-3 FS-exec loader (M2 argv-frame work)

## Symptom

A small `u64 -> u64` helper called from another function returned `0` for an
argument that is provably **in range**, causing its `== 0` failure guard to
fire. The exact helper (since deleted in favour of an inline path):

```simple
fn _top_phys_for_vaddr(top_phys: u64, stack_top: u64, vaddr: u64) -> u64:
    val PAGE: u64 = 4096
    val top_page_base = stack_top - PAGE
    if vaddr < top_page_base or vaddr >= stack_top:
        return 0
    top_phys + (vaddr - top_page_base)
```

Called with `stack_top = 0x8000200000`, `vaddr = 0x80001FFFE0`
(`top_page_base = 0x80001FF000`). The vaddr is clearly inside
`[0x80001FF000, 0x8000200000)`, yet the function returned `0` — i.e. the guard
`vaddr < top_page_base or vaddr >= stack_top` evaluated **true**. QEMU serial:
`[spawn] argv-frame fail: write64 min argc` on the very first stack write.

## CONFIRMED root cause (2026-07-08)

The inline rewrite that replaced the helper *also* miscompiled at first — until
every `.to_u64()` on an integer **literal** was removed. `(STACK_TOP_U -
64.to_u64()) & (~(15.to_u64()))` produced `rsp=0x2000000000000000`-class garbage;
rewriting as typed `u64` locals + **bare** integer literals
(`(STACK_TOP_U - 64) & ALIGN_MASK`, `ALIGN_MASK: u64 = 0xFFFFFFFFFFFFFFF0`)
produced the correct `rsp=0x80001FFFC0`, `off=0xFC0`, and a `0xDEADBEEFCAFEF00D`
sentinel roundtrip. So the trigger is **`.to_u64()` / `.to_i64()` applied to an
integer literal under freestanding native-build — it boxes/tags the literal, and
subsequent arithmetic operates on the tagged representation.** The cross-function
helper hit the same class through its u64 params/locals. `_map_pt_loads` was
always correct because it uses typed `u64` locals and bare literals throughout.

**Fix pattern for freestanding code:** never write `<intliteral>.to_u64()`. Use a
typed `val X: u64 = <literal>` or a bare literal in u64-typed arithmetic.

## Scope / isolation

- The SAME arithmetic done **inline in the caller's own scope** (see
  `_map_pt_loads` and the current inline frame builder in
  `src/os/kernel/loader/x86_64_fs_exec_ring3.spl`) works correctly — direct
  `mmio_write8(phys + off, …)` with locally-computed offsets is fine.
- Only the CROSS-FUNCTION form failed. Two candidate root causes, not yet
  disambiguated:
  1. **u64 parameter passing** truncating/boxing a wide argument at the call
     boundary under freestanding native-build, or
  2. the **`a < b or a >= c` u64 comparison** itself mis-lowering (e.g. signed
     vs unsigned compare, or the boolean `or` short-circuit) in freestanding.

## Minimal repro (to build)

A freestanding native-build unit that calls a `fn f(a: u64, b: u64, c: u64) -> u64`
returning `0` when `a < b or a >= c` else `a`, with `a` strictly inside `[b, c)`,
and asserts `f(0x80001FFFE0, 0x80001FF000, 0x8000200000) == 0x80001FFFE0`.
Compare interp vs freestanding native-build output.

## Workaround in place

`src/os/kernel/loader/x86_64_fs_exec_ring3.spl` builds the SysV initial frame
inline via direct-phys mmio in the caller scope (no cross-function u64 helper,
no range guard — the offset is in-page by construction). This unblocked the
ring-3 argv frame (M2) but does not fix the underlying codegen bug.

## Impact if unfixed

Any freestanding/baremetal Simple code that factors u64 range math into a helper
can get silently-wrong results. This is a correctness landmine for the OS,
drivers, and firmware layers that run under freestanding native-build.
