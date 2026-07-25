# BUG: x64 freestanding if-EXPRESSION phi-merge corrupts extern-`[u8]` branch handle

**Status:** ROOT-FIXED 2026-07-10 (see "Root cause + fix" below). Workaround at
ssh_session_kex.spl:565 is now removable.
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

## Root cause + fix (2026-07-10) — NOT a type/merge bug

The merge is structurally correct in MIR. The actual defect is in Cranelift
codegen block scheduling: `codegen/instr/body.rs` compiles blocks in
`func.blocks` **storage order** and populates `local_addr_map`
(VReg→local_index, from `LocalAddr`) **lazily** as each block is compiled.
After a `Simple`-fn branch is **inlined**, the if-EXPRESSION condition block
(which emits the merge slot's `LocalAddr`) can be renumbered to a HIGH block id
stored AFTER the low-id then/else/merge blocks that consume it. When those
consumer blocks are compiled first, `local_addr_map` lacks the merge-slot VReg,
so the merge `Store`/`Load` fall through to the raw-address path and silently
mis-resolve — corrupting the extern-`[u8]` handle. This is why P9 (Simple-fn
untaken branch → inlining → id inversion) fails while P8 (both extern, no
inline) and P10 (if-STATEMENT, pre-declared local) pass, and why the failure is
nondeterministic (garbage address).

**Fix:** pre-populate `local_addr_map` from *every* `LocalAddr` in the function
before compiling any block (`LocalAddr` is a pure, SSA-unique
`dest → local_index` fact, so this is order-safe for all backends/targets).
One change in `codegen/instr/body.rs`; no lowering change; interpreter/rv64/
hosted unaffected. abi_probe P9 now reads correctly; P1-P8/P10 unchanged; lib
unit-test failure set unchanged vs baseline (238 vs 239, delta is flaky
watchdog test only).

## 2026-07-10 update — x64 SSH login now completes end-to-end

The SSH `incorrect signature` failure root-caused to TWO defects (source-level
workarounds applied; compiler root fixes still pending):

1. **Chained-method mis-lowering (new class).** In `ssh_session.spl`
   `do_version_exchange`, `our_version.len().to_i64()` (chained method call)
   mis-lowers on x64 freestanding native-build and yields garbage
   (`1153202244875779923` instead of `22`) — the documented "chained methods
   broken" limitation surfacing in codegen. `rt_bytes_slice(our_version, 0,
   garbage-2)` then received `length=0` and returned an EMPTY
   `server_version_bytes`, so the exchange-hash transcript omitted the server
   version → hash mismatch → client rejected the signature. Fix: bind
   `val ov_len = our_version.len()` first, then `ov_len.to_i64() - 2`.

2. **Extern-`[u8]`-return store class (this bug).** The landed if-statement
   workaround still stored the extern return directly into a typed var
   (`exchange_hash = rt_ssh_curve25519_exchange_hash(...)`). Root-safe form: pass
   the extern return straight through `_copy_bytes_stable(...)` (the idiom used
   everywhere else) so the destination holds a Simple-built packed copy. Applied
   at the exchange-hash site and at the `server_version_bytes` field store.

**The "0x53 clobber" (defect (b) as originally reported) is NOT data
corruption.** Serial `_bytes_to_hex(exchange_hash)` / `_bytes_to_hex(sig_raw)`
print `0x53…` garbage, but the underlying bytes are correct — proven because a
real OpenSSH client verifies the ed25519 signature and runs `true` to
`Exit status 0`. The `0x53` pattern is a **`_bytes_to_hex` display-only misread
of packed `[u8]`** (separate, cosmetic; TODO: fix the hex-dump helper's
packed-array read). A C-side print at return proved the array is correct in
memory (packed, `gc_flags=0x08`, correct data 0x94,0x48,0x8f…).

**Gate result:** `ssh -p 2222 root@127.0.0.1 true` (password `simpleos`)
completes full KEX → NEWKEYS both ways → password auth → channel → command →
`debug1: Exit status 0`. No `incorrect signature`.
