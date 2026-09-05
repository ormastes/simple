> # REOPENED 2026-08-08 — this doc's verdict is WRONG (its measurement is not)
>
> A tiebreaker lane re-ran both probes with proven edit-visibility. The defect
> is **REAL**. This doc measured only the `bin/simple run` path, where the
> import genuinely succeeds. On the `bin/simple test` (interpreter) path the
> same full-path import fails at module load with
> `error: semantic: variable noalloc not found`, `no examples executed`.
>
> - **Discriminator:** `bin/simple run` vs `bin/simple test`. NOT the facade,
>   NOT the `export use` re-export — a spec importing the noalloc package by
>   full path with no facade involved fails identically.
> - **Root cause:** `@noalloc` was never registered in any parser. The Rust
>   seed interpreter evaluates an unrecognised `@X` as a runtime decorator, so
>   it looked up the bare identifier `noalloc` and failed.
> - **Keep from this doc:** the `run`-path result below is correct and
>   reproducible. **Discard:** the title, the "closed, not a defect" status,
>   and every statement that the error "does not reproduce in any form".
> - **Fixed in source** 2026-08-08 (`interpreter_eval.rs` decorator skip-list);
>   not yet deployed.
>
> Superseded by
> `doc/08_tracking/bug/noalloc_decorator_unbound_in_seed_interpreter_2026-08-08.md`.

# FALSE ALARM: "`@noalloc` annotations don't survive import" — the cause was ordinary facade shadowing

**Status: closed, not a defect.** No compiler change was needed or made.

## The claim

A lane reported that importing from a module carrying `@noalloc` annotations
fails with `semantic: variable 'noalloc' not found`, and that an A/B test had
established this:

> `use std.hash.{fnv1a_hash_i64}` and
> `use std.nogc_async_mut_noalloc.hash.{fnv1a_hash_i64}` **both** fail
> identically with that error, with and without an intervening facade — so
> this, not facade shadowing, is why those four hash functions are unreachable.

The claim was written into the header of the working-copy-only facade file
`src/std/hash.spl`, where it was being used to justify NOT re-exporting the
four symbols (`fnv1a_hash_bytes`, `fnv1a_hash_i64`, `crc32_byte`,
`crc32_bytes`) that the facade shadows. It also carried a second claim: that
re-exporting them "would make the trait half fail as well (the broken module
poisons the whole facade)".

## Re-measured 2026-08-08: every part of the claim is wrong

Probes kept **inside** the repo (`probe/dfx/`), because an entry outside the
repo re-roots `std.*` and would itself manufacture an import failure.

| Probe | Result |
|---|---|
| `use std.nogc_async_mut_noalloc.hash.{fnv1a_hash_i64}` | **SUCCEEDS** — prints `-55488592825689361` |
| `use std.hash.{fnv1a_hash_i64}`, facade file moved aside (= exactly origin/main, where `src/std/hash.spl` does not exist) | **SUCCEEDS** — same value |
| `use std.hash.{fnv1a_hash_i64}`, facade present without the re-export | fails — `function fnv1a_hash_i64 not found`, with a `[use-warning]` naming `src/std/hash.spl` as the module that "does not provide it" |
| `use std.hash.{fnv1a_hash_i64}` + `use std.hash.{hash_combine}`, facade present WITH the re-export added | **both SUCCEED** — no poisoning |

`semantic: variable 'noalloc' not found` did not reproduce in any form.

### The measurement was verified, not assumed

The success results are only meaningful if the run actually read
`src/lib/nogc_async_mut_noalloc/hash/mod.spl` from disk — otherwise the
`@noalloc` annotations were never parsed and the run proves nothing about
them. Confirmed by sabotage: mutating `FNV1A_PRIME` in that file changed the
printed hash (`-55488592825689361` -> `798661336609459599`), so no bundled
stdlib was being served. The sabotage was reverted.

## Conclusion

There is no `@noalloc` import defect. The `nogc_async_mut_noalloc` tier's
annotated modules import fine, both by their full path and via `std.hash`.

The sole cause of the four hash functions being unreachable was the facade
`src/std/hash.spl` winning the `std.hash` name (`src/std` is a symlink to
`lib`) and not re-exporting what it shadowed — **ordinary facade shadowing,
which the old comment explicitly denied**. Fix is one line in that facade:

```
export use nogc_async_mut_noalloc.hash.{fnv1a_hash_bytes, fnv1a_hash_i64, crc32_byte, crc32_bytes}
```

That line and a corrected header have been applied to the working copy. The
facade file itself is not landed here: it does not exist on `origin/main` and
is owned by a concurrent session, so overwriting it from this lane would risk
clobbering that session's in-flight work.

## What this unblocks

- **The noalloc tier's importability** — never actually blocked. Any lane that
  was waiting on a compiler fix before importing from
  `nogc_async_mut_noalloc` can proceed now.
- **The facade-audit lane** — can proceed, and should treat this as a worked
  example: the audit rule is that a facade must re-export the full set of
  names it shadows. Nothing about the shadowed module's annotations exempts it.

## Process note

The original A/B test reached the opposite conclusion on both directions of
the comparison. The most likely explanation is that it was run with an entry
point outside the repo (which re-roots `std.*`), or against a tree where the
facade was present in both arms — in which case both arms fail for the facade
reason and look "identical", which is exactly the observation reported. When
an A/B says "identical failure with and without X", check that the two arms
really differed in X.
