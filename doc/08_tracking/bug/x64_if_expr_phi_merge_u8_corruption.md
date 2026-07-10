# BUG: x64 freestanding if-EXPRESSION phi-merge corrupts extern-`[u8]` branch handle

**Status:** open (workaround landed at the one KEX-critical site)
**Severity:** high (silent heap-handle corruption; any if-expression mixing extern and Simple `[u8]` branches)
**Component:** seed native-build codegen — `lower_if_expr` (src/compiler_rust/compiler/src/mir/lower/lowering_expr_control.rs:69)
**Found:** 2026-07-10, x64 SSH KEX bring-up

## Symptom

On x86_64 freestanding native-build (seed, cranelift), an `if`-EXPRESSION whose
branches mix an extern-`[u8]`-returning call (ANY-erased across the C facade)
with a Simple-fn `[u8]` return corrupts the taken extern branch's result
handle. Reproduced by `abi_probe` P9 (examples/09_embedded/simple_os/arch/
x86_64/abi_probe_entry.spl): `handle=0x15/0x16` (nondeterministic, not a valid
TAG_HEAP pointer), `len=garbage`. The equivalent if-STATEMENT assigning into a
pre-declared `var` is clean (P10: handle/len/reads all correct).

## Analysis

`lower_if_expr` merges branch results through Store/Load slots that are
type-agnostic; the extern branch's value register itself is clobbered in the
merge. The statement path (lowering_stmt.rs assignment into an existing local)
does not use the buggy merge.

## Repro

`sh scripts/os/abi_probe_run.shs` → grep `-a` P9/P10 in
build/os/abi_probe.serial.log. P9 = bug (intentional repro kept as a
regression canary: when P9 reads correctly, the bug is fixed and the probe
should be updated), P10 = clean pattern.

## Workaround (landed)

src/os/apps/sshd/ssh_session_kex.spl:565 — exchange-hash selection converted
from if-expression to if-statement into `var exchange_hash =
_zeroed_32_bytes()`. Other if-expression sites mixing extern/Simple `[u8]`
branches remain at risk until the codegen fix.

## Fix direction

Make the `lower_if_expr` result merge preserve the branch value representation
(type-aware slot or direct register move), or route erased-`[u8]` results
through the same recovery used for typed indexing (see landed
lowering_expr_struct.rs `recovered_receiver_ty` fix in 19e2f81e).
