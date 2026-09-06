# The aarch64 JIT arena is never unmapped, and the vendored edit that added it is unguarded

**Filed:** 2026-09-06
**Severity:** medium — a leak bounded by process lifetime, plus a process gap that
silently reverts the fix
**Area:** `src/compiler_rust/vendor/cranelift-jit/src/memory.rs` (vendored, edited
in-tree by `f949a37b217` / PR #423)

Follow-ups to the relocation fix in
`jit_aarch64_branch_relocation_out_of_range_abort_2026-09-05.md`. **The fix
itself is correct** — the `diff >> 25` predicate, the veneer encoding, and the
x16 clobber were each re-derived independently and hold. What follows are the
things the fix left behind. Filed rather than patched: changing an allocator
under a JIT deserves its own reviewed change, not a drive-by.

## 1. The arena is never unmapped (verified)

`git grep munmap` over the whole crate returns **zero hits**, and
`ARENAS: Mutex<Vec<Arena>>` never removes entries. `Memory::free_memory`, whose
doc comment at `memory.rs:607` reads *"Frees all allocated memory regions that
would be leaked otherwise"*, is guarded at `:112` by

```rust
if !self.ptr.is_null() && !self.from_arena {
```

so on aarch64 Linux — where code allocations now carry `from_arena: true`
(`:471`) — it frees nothing. The documented API contract is not met on the one
platform the arena exists for.

Bounded by process lifetime, and `bin/simple` is short-lived, so this is not
urgent. It matters for any long-lived host that JITs repeatedly (LSP, MCP
server, test daemon), which are exactly the processes this repo runs warm.

## 2. Exhaustion degrades to an abort, not to corruption

When `alloc_code` returns `None`, `use_arena` is set `false` **permanently**, so
every later chunk comes from the heap — reintroducing the original
gigabytes-apart hazard. `install_far_call_veneer` then returns `None` because
the call site is in no arena, and the new `assert!(fits(diff), ...)` panics
inside `finalize_definitions`. Safe (it aborts rather than branching to a wrong
address) but abort-shaped. `MIN_CHUNK = 64 KiB` per `finish_current()` round
caps this at roughly 2048 rounds, and `compile_module` finalizes once per module
(`jit.rs:213`), so practical risk is low.

Separately, `publish_veneers` calls `.expect()` while holding the arena mutex, so
a failure there poisons the lock and panics the process later.

## 3. The vendored edit survives no `cargo vendor` refresh (verified)

The fix is a direct in-tree edit of `vendor/cranelift-jit/**` with a regenerated
`.cargo-checksum.json`. There is no patch file, no `build.rs` application step,
and no guard. `cargo vendor` silently reverts it, and nothing fails afterwards —
the JIT simply goes back to admitting +/-256 MiB.

Worse, **CLAUDE.md's Owned-Code Scope (line 55) lists
`src/compiler_rust/vendor/**` as external**, so every code count, review,
verification scan and census in this repo is instructed to skip exactly this
code. The one place carrying a load-bearing local patch is the one place nobody
looks.

Minimum viable guard: a check that asserts the two patched files still hash to
the patched values, so a `cargo vendor` refresh fails loudly instead of silently
undoing the fix.

## 4. The veneer path has zero test coverage

`abi.rs:1044` routes `RelocDistance::Far` to `LoadExtName` + `CallInd`, so
`Arm64Call` only ever targets colocated code — inside the arena, always in range.
The veneer path therefore fires only on arena exhaustion or with
`SIMPLE_JIT_FORCE_VENEERS=1`. No test was added (`tests/basic.rs` is unchanged),
and the whole `aarch64_arena` module is `cfg(aarch64, linux)`, so x86_64 CI never
compiles it, let alone runs it.

The forced-veneer runs recorded in the original bug (3 runs, 10,155 veneers
installed per run, 0 failures) are the only evidence this path works, and they
are not automated.

## What was checked and is fine

No silent corruption path was found: veneers grow down, code grows up, guard
pages use `align_down(self.high, ps)`, there is no overlap and no post-hoc offset
shifting. W^X holds — the arena is mapped `PROT_READ|PROT_WRITE` and only made RX
after relocation, and `publish_veneers` snaps `self.high = start` so no page is
written after publication.
