# `.unwrap()` still rebinds to `Poll.unwrap` at closure scale via a second route (2026-09-13)

Status: OPEN. Residual of
`stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md` (PR #750), which
is RESOLVED for the site it names and NOT for the whole population.

## Measurement — this is the honest number

PR #750 guarded `mangle_mir`'s two bare `.method` scans. Counting `bl` edges to
`_lib__nogc_async_mut__async__poll__Poll.unwrap` in the Stage 2 candidate,
before and after, on this host:

| | call sites | distinct calling functions |
|---|---|---|
| run 15 candidate (before) | 270 | 144 (incl. `Poll.unwrap`'s own frame) |
| run 17 candidate (after) | **208** | **109** |

So PR #750 cleared 62 sites — including the one that mattered,
`find_linker_path`, which now correctly reads `bl <_rt_unwrap_or_trap>` — and
**208 remain**. Zero legitimate external `Poll.unwrap` callers exist in this
tree, so essentially all 208 are miscompiled the same way: a `.unwrap()` that
should lower to the builtin is calling an unrelated type's method, which returns
0 for a non-`Poll` receiver.

**Correcting the record:** PR #750's body and the predecessor's RESOLVED section
describe the 270-site blast radius in a way that reads as if the fix cleared all
of it. It cleared 62. That overstatement is corrected here and in those
documents.

## What is already ruled out — do not re-test these

With the PR #750 seed, in a 2-unit closure that DOES contain a competing user
method named `unwrap` (the ingredient without which nothing reproduces at all),
every one of these prints correctly:

```
val p = find_it(); if p.?: Ok(p.unwrap())      -- the original blocker shape
val a: text? = "/annotated"; a.unwrap()        -- explicitly annotated local
opt_call().unwrap()                            -- direct call receiver
res_call().unwrap()                            -- Result receiver
h.slot.unwrap()                                -- struct field receiver
opt_call().unwrap().trim()                     -- chained
rv.unwrap()                                    -- the genuine user method, still correct
```

So the residual route needs something a 2-unit closure does not have. The
reproducer harness is `repro/{rival,main}.spl` + `repro.sh` (2.6 s per
iteration); extend it rather than starting over.

## Leading hypothesis (NOT confirmed)

`resolve_call_target` (`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs`)
has its own qualified-name fallback with **no** enum-helper guard and no type
restriction:

```rust
let candidates = local_suffix_index.get(lookup_name)
    .or_else(|| suffix_index.get(lookup_name))
    .or_else(|| local_suffix_index.get(method))   // qualifier DISCARDED
    .or_else(|| suffix_index.get(method));
let best = candidates.iter().find(|c| c.to_lowercase().contains(&type_part.to_lowercase()))
    .or_else(|| if candidates.len() == 1 { candidates.first() } else { None });
```

A qualified `text.unwrap` skips the bare guard (it contains a dot), fails
`resolve_name_variants`, matches no candidate containing "text", and is then
returned by the single-candidate arm. The `resolve_by_suffix` fall-throughs
immediately below have the same shape. `codegen/llvm/functions/calls.rs`
(module-wide `.unwrap` scan, shortest name wins) is a second candidate, reachable
for an already-qualified name, since `bare_rt_redirect` fires only on exactly
`"unwrap"`.

This is a hypothesis because the 2-unit probes above did NOT produce a qualified
`text.unwrap` — the route that generates one has not been identified.

## Suggested next step

1. Pick one residual caller (list below) and disassemble it to see what feeds
   `x0` before the `bl` — the receiver shape is the thing to reproduce.
2. `resolve_call_target` is a standalone function like its twin, so it is
   unit-testable exactly the way
   `text_qualified_enum_helpers_never_rebind_to_a_lone_user_method` tests
   `resolve_method_call_static`. Write the test first.
3. Guard the single-candidate arm and the `resolve_by_suffix` fall-throughs with
   `is_enum_helper_method`; check whether `calls.rs` needs it too.
4. Verify by re-counting `bl …Poll.unwrap` on the next Stage 2 candidate — the
   number should fall to 0 external callers. **Count the instruction; do not
   infer from a passing verdict.**

Sample residual callers (109 total):

```
MirToLlvm.lookup_function_return_unsigned
MirToLlvm.translate_module_with_entry_policy
MirToLlvm.llvm_format_span
cranelift_codegen_adapter.compile_function
cranelift_codegen_adapter.cranelift_static_init_bits_value
cranelift_codegen_adapter.cranelift_static_init_supported
```

## Why this did not block Stage 2

Stage 2 builds and now reaches a real link failure (`-lc`, see
`stage2_sanity_darwin_link_passes_lc_2026-09-13.md`). These 208 sites are latent:
each returns 0 where a payload was expected, and only bites when the value is
used in a way that notices. `find_linker_path` noticed. The rest are unexploded.

## Related

- `doc/08_tracking/bug/stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md` (predecessor)
- `doc/08_tracking/bug/stage2_sanity_darwin_link_passes_lc_2026-09-13.md` (current Stage 2 blocker)
- PR #750
