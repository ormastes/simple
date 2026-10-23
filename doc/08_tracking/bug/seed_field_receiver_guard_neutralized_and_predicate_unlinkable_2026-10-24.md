# The seed's struct field-receiver guard is disabled by default, and its predicate is not linkable from the seed at all

- **Date:** 2026-10-24
- **Status:** OPEN
- **File:** `src/compiler_rust/compiler/src/codegen/instr/fields.rs`
- **Severity:** a safety guard is off by default in the seed JIT/codegen; and the
  constraint behind it invalidates the recorded fix path for
  `cranelift_cmov_memory_operand_unconditional_load_2026-10-23.md`

## What is committed

```rust
// LOCAL BUILD NEUTRALIZATION (not committed): the receiver guard calls
// rt_struct_receiver_valid, which lives only in runtime_native.c — a TU
// the seed crate cannot link (duplicate rt_host_gpu_* symbols). Until the
// guard lane lands the seed-side symbol, emit no guard so the JIT keeps
// the pre-guard behavior. Revert via /tmp/fields_rs_guarded.rs.
if std::env::var("SIMPLE_SEED_FIELD_GUARD").is_err() {
    return Ok(());
}
```

Three separate problems in one block:

1. **The guard is OFF by default.** `guard_nonnull_receiver` has 3 call sites and
   all of them return immediately unless `SIMPLE_SEED_FIELD_GUARD` is set in the
   environment of the compiler process. So field loads/stores in seed-built code
   are unvalidated, and the named-diagnostic-then-trap path
   (`rt_eprintln_str` + `TrapCode 12`) that the comment describes does not run.
2. **A comment claiming "(not committed)" is committed.** It describes itself as
   a local build hack; it is in `release/1.0.0`.
3. **Its revert instructions are unrecoverable.** "Revert via
   /tmp/fields_rs_guarded.rs" — that file does not exist. `/tmp` does not
   survive, so the guarded version the comment points to is gone.

## The constraint that matters beyond this file

The stated reason is the important part: **`rt_struct_receiver_valid` lives only
in `runtime_native.c`, a translation unit the seed crate cannot link** because of
duplicate `rt_host_gpu_*` symbols.

That invalidates the fix path recorded in
`cranelift_cmov_memory_operand_unconditional_load_2026-10-23.md`, which proposed
routing `emit_aggregate_block_copy`'s validity predicate through
`rt_struct_receiver_valid`. It is not merely a question of ordering (register
with `rt_struct_alloc` first, as that record now says) — **the symbol is not
available in the lane that builds Stage 2 at all**. Anyone implementing it there
will hit the same link failure that caused this neutralization.

This also explains why the copy-in predicate is a tag/address heuristic rather
than a registry lookup: the authoritative predicate is unreachable from that
crate. Fixing the copy-in soundly therefore requires one of:

- landing `rt_struct_receiver_valid` (or an equivalent) as a seed-linkable
  symbol — the "guard lane" the comment refers to, which has not landed; or
- a predicate that needs no runtime call and is target-agnostic. Note that the
  obvious candidate, an address-range check, is already recorded as harmful:
  SimpleOS links higher-half, so `< 2^48` rejects every kernel heap pointer and
  silently degrades value semantics.

## Provenance

`git log -S'LOCAL BUILD NEUTRALIZATION'` attributes the block to
`6a7a7020dfc fix(ui): restore widget chrome + JIT-lane fixes clobbered by
775ae478ca` — i.e. it rode in on a commit repairing a previous clobber. That
makes it a fifth instance of the pattern already tracked on this branch
(`facet_abi.spl`; the dangling `flat_pool_debug_state_v1` call; `codec_gen.spl`
older than its output; four dropped `fold_gen` functions): work lost or
distorted by a merge/rewind and only noticed later.

## Suggested next steps

1. Decide whether the guard should be on. If yes, the blocker is the seed-side
   symbol, not this file; if no, the comment should say so plainly instead of
   describing itself as an uncommitted local hack with a `/tmp` revert.
2. Reconstruct the guarded version from this file's own code (the `err_block` /
   `ok_block` sequence below the early return is intact) rather than from the
   lost `/tmp` copy.
3. Record the `rt_host_gpu_*` duplicate-symbol problem as its own item if it is
   not already tracked; it is the actual blocker for both this guard and any
   registry-based copy-in predicate.
