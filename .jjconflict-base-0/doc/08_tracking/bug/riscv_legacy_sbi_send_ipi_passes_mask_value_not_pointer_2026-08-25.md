# RISC-V legacy SBI `send_ipi` passes a hart-mask value where the ABI requires a pointer

- **Status:** SOURCE-FIXED, EXECUTION UNVERIFIED
- **Filed:** 2026-08-25
- **Area:** RV64 bare-metal SBI IPI dispatch
- **Severity:** critical — the selected legacy IPI path can give firmware an invalid
  address instead of the required in-memory hart-mask word
- **Evidence level:** static source review only; no build, test, benchmark, emulator,
  firmware, or hardware execution was performed for this report

## Defect

The deprecated legacy SBI IPI extension (`EID = 0x04`) takes one argument: a
pointer to a hart-mask word in supervisor memory. This repository's intended
contract records that pointer ABI in all three relevant places:

- `src/lib/nogc_async_mut_noalloc/baremetal/riscv/sbi.spl:9-12` describes
  legacy `0x04` as having a single `hart_mask_ptr` argument.
- `src/lib/nogc_async_mut_noalloc/baremetal/riscv/sbi.spl:95-97` declares
  `sbi_send_ipi_legacy(hart_mask_ptr: u64)` and forwards that argument in `a0`.
- `doc/05_design/app/riscv/riscv_smp_cache_hal.md:98-105` specifies that the
  legacy path passes the hart mask **on the stack**.

The production dispatcher does not create such a word or take its address.
When the cached path is legacy and `hart_mask_base == 0`, it passes the numeric
mask directly:

```simple
if hart_mask_base == 0u64:
    sbi_send_ipi_legacy(hart_mask)
```

This is at
`src/lib/nogc_async_mut_noalloc/baremetal/riscv/sbi.spl:123-127`.
Consequently, a request with `hart_mask = 1` puts `1` in `a0`; legacy firmware
interprets `a0` as an address from which to load a mask word, not as the mask
word itself. The code therefore violates both its declared production contract
and its design.

The target leaf preserves this mismatch rather than correcting it:
`src/os/kernel/arch/riscv64/boot/freestanding_runtime.c:134-150` copies the
caller's numeric `arg0` directly into register `a0` and issues `ecall`.
Production HAL reachability is explicit in
`src/os/kernel/arch/riscv64/hal_smp.spl:25,181-188,190-213`: the HAL imports
`sbi_probe_then_send_ipi`, calls it for a single-target send, and calls it for
each nonempty broadcast mask window.

## Scope and impact

The defective branch is reached when:

1. the v0.3+ IPI extension probe fails;
2. the legacy `0x04` extension probe succeeds, selecting the cached
   `IpiPath.Sbi_legacy`; and
3. the send request has `hart_mask_base == 0`.

Those selection branches are at `sbi.spl:74-81,117-127`. The v0.3 path passes
mask value plus mask base and is not this pointer defect. A legacy selection
with a nonzero base currently expands the sparse mask into CLINT MMIO writes
(`sbi.spl:128-136`) and also avoids this exact call.

On the affected path, firmware may read an invalid or unintended low address,
raise an access fault, reject the call, target the wrong harts, or deliver no
IPI. The resulting symptoms include failed secondary-hart wakeups, missed
cross-hart notifications, stalls, or nondeterministic SMP behavior. The failure
is especially direct for ordinary masks such as `0x1`, `0x2`, or `0x4`, which
become implausible pointer addresses.

## Existing unit spec does not cover production

`test/01_unit/lib/baremetal/riscv/sbi_ipi_spec.spl` imports only
`sbi_ipi_absolute_hart` (`:8-9`). It locally reimplements the probe and send
mocks (`:26-89`) instead of calling the production dispatcher or intercepting
the production `rt_riscv64_sbi_call` boundary. In particular:

- the local legacy mock at `:87-89` ignores its argument and always returns
  success;
- the local dispatcher at `:77-81` merely records `(hart_mask,
  hart_mask_base)`; and
- the legacy examples at `:132-143,177-181` never prove that production `a0`
  is a dereferenceable address containing the requested mask.

These tests can remain green while production passes the value as a pointer.
Comments at `:14-19,56-58` also describe intended production wiring that the
file does not perform.

## Correct fix options

Pure Simple must remain the owner of extension probing, cached path selection,
mask/base policy, fallback choice, and error handling. Two implementation forms
can preserve that ownership:

1. **Preferred when the RV64 freestanding backend has a proven typed stable
   address operation:** create a local `u64` mask word in `sbi.spl`, take its
   actual address, and pass that address to `sbi_send_ipi_legacy`. The word must
   remain live through the synchronous ecall. Do not assume that an `any`-typed
   `unsafe_addr_of` produces the address of unboxed scalar storage; that ABI must
   be proved before use.
2. **Narrow ABI-leaf fallback:** expose a specifically named runtime primitive
   that accepts the mask by value, creates one native stack word in the C/asm
   ABI leaf, and issues legacy `EID 0x04` with the word's address in `a0`. The
   leaf must not probe extensions, cache or select paths, iterate harts, choose
   CLINT, or otherwise absorb Simple policy.

If neither pointer-safe form is immediately available, fail closed by disabling
the legacy selection and using the existing CLINT path where that fallback is
valid. Passing a mask value as a pointer must not remain as a compatibility
shortcut.

## Required verification and coverage

Acceptance needs a test seam at the **production** ecall boundary. For the
legacy/base-zero call, it must observe `EID == 0x04`, `FID == 0`, prove that `a0`
is an address rather than the mask value, and safely read the word at `a0` to
confirm it equals the requested mask. Include zero, one-bit, multi-bit, and
high-bit masks, and keep the word alive until the intercepted ecall returns.

Real branch and condition coverage must execute production code for:

- initial `IpiPath.Unavailable`/uninitialized state versus an already
  initialized cached-path state;
- v0.3 probe success;
- v0.3 failure followed by legacy success;
- both probes failing and selecting CLINT;
- v0.3, legacy, and CLINT dispatch arms;
- legacy `hart_mask_base == 0` and `!= 0`;
- zero and nonzero mask bits in the legacy-nonzero-base and CLINT loops;
- valid absolute hart calculation and overflow rejection; and
- success and error returns at the production SBI boundary if errors are
  surfaced by the repaired API.

Mock-only helper logic is insufficient. In addition to unit interception, retain
an RV64 OpenSBI-backed execution artifact that forces the legacy branch, or an
equivalent firmware harness that implements the legacy pointer ABI. Hardware or
emulator evidence must identify the firmware, artifact, command/configuration,
exit result, and observed target harts. Coverage and execution remain pending;
this report does not claim either.

## Performance and memory constraint

The **already-cached legacy/base-zero hot branch** must remain `noalloc` and
constant-time: one synchronous legacy ecall, no reprobe, no mask scan, and at
most one 8-byte address-taken hart-mask object on RV64. The generated stack
frame or stack-usage delta may be larger because of ABI alignment. The cold first send
is different: `sbi.spl:119-120,66-81` lazily initializes `IPI_PATH`; selecting
legacy performs the v0.3 probe ecall, the legacy probe ecall, and then the
legacy send ecall. The repair must preserve those existing hot/cold operation
counts unless a separately justified design changes initialization.

The repair must add no heap allocation, growable collection, persistent
per-send state, or per-send static-memory growth. Its code-size increase must be
fixed, with no generated/unrolled per-hart tables; verification should record
the linked text-size delta and the actual compiler-reported or otherwise
measured alignment-rounded frame-size/stack-usage delta.
Resident-set size is not a bare-metal runtime metric. If relevant to the build
or emulator workflow, report hosted compiler/emulator peak RSS separately,
along with measured latency, as new evidence rather than inferring it from this
static review.

## Unblock condition

Close this bug only after the value-versus-pointer mismatch is repaired without
moving IPI policy out of Pure Simple, the production-boundary tests cover the
listed conditions, and retained firmware-backed evidence demonstrates correct
legacy IPI delivery. Updating only the local mocks does not satisfy closure.

## Source fix (2026-08-26)

The production dispatcher now creates one local `u64` mask word, takes its
address inside a minimal `raw_ptr` capability region, and passes that address
to the synchronous legacy ecall. A nonzero hart-mask base uses CLINT instead;
that fallback now adds the base, rejects values outside `u32`, and stops once
the remaining mask is zero. No heap allocation or extra foreign call is added.

The focused static ratchet records this source shape, but the production ecall
interception, OpenSBI/QEMU behavior, and exact signed artifact remain unproven.
Accordingly this issue is not labeled verified or closed.
