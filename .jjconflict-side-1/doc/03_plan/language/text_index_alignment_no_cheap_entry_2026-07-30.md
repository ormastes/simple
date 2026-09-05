# Text-index CHARACTER alignment has NO cheap first step

Campaign status statement. Companion to
`text_index_alignment_rescope_2026-07-30.md` and its addendum.

## The finding

**Every entry point into this migration costs one of three things:**
a vectorization decision, an offset-drift hazard, or a ~56-file
synchronized change. There is no small safe primitive to start with.

This is not a reason to abandon the alignment — the silent-corruption
families it fixes are real — but it means the work is **one large
coordinated change, not a staged migration**, and the plan should say so
rather than implying a gentle ramp.

## How each candidate was eliminated (definition censuses, not call sites)

| Primitive | Verdict |
|---|---|
| `char_at`, `char_code_at` | Already CHARACTER-indexed. Not targets — they are the 79-site **guard population**. |
| `bytes` | Byte-by-intent. Excluded by scope: the decision was to make *indexing* agree, not to erase byte-level APIs. |
| `slice`, `substring` | Carry offset parameters -> offset-drift hazard applies. |
| `index_of` (2-arg) | Offset parameter, **and** SIMD-backed via `rt_string_find`. |
| `last_index_of` | **SIMD-backed** — 42 last-search matches in `runtime_simd_search.c`, plus a dedicated `lib/common/encoding/simd_text_ffi.spl`. Spread also includes `runtime/src/value/collections.rs` (x2), `string_core.spl`, `lib/text.spl`, `core_array_query.spl`, `os/apps/shell/shell_expand.spl`, `lib/js/node/path_module.spl`, two `test_runner` files. |
| `len` / `length` | The ONLY primitive clean on units: no offset parameter, no SIMD path, plentiful multi-byte call sites. But ~56 implementation files across 12+ tier directories, and it is the loop bound for every scan — which is why it was sequenced last. |

**The criteria are in direct conflict:** everything small enough is
already character-indexed, byte-by-intent, offset-carrying, or
vectorized; the one primitive that is clean on units is the largest
surface in the campaign.

## `length` cannot be peeled off from `len` (PROVED)

The last remaining hope for a cheap entry was migrating `length` alone as
an alias-layer change. It does not exist as a separable change.
`length` is not a wrapper around `len` — it is an **alias sharing the
identical code path**:

- `compiler_rust/compiler/src/interpreter_method/string.rs:21` —
  `"len" | "length" => return Ok(Value::Int(s.len() as i64))` (one arm).
- `hir/lower/expr/mod.rs` — comments record `length` as "a documented
  synonym of `len`"; codegen tables read `"len" | "length" => "rt_len"`;
  the return-type table reads `"len" | "length" => Some(TypeId::I64)`.

Migrating `length` **is** migrating `len`. No seam exists to cut at.

## Consequence for the campaign

1. The first semantic change will be `len`/`length` across ~56 files, or
   it will be a primitive that first forces the SIMD boundary-conversion
   decision. Choose deliberately; there is no third option.
2. Because `len` is the loop bound for every scan, migrating it first
   inverts the plan's ordering rationale (it was scheduled last for
   exactly that reason). If it is nevertheless chosen as the entry, the
   staged order collapses into a single coordinated change.
3. The prerequisites do not go away: the census re-run accounting for the
   `compilability.rs` gate is still needed for sizing, and the
   offset-drift rule still binds every primitive taking an index.

## Open items (unresolved)

- Four scanner bodies still unread and unclassified (listed in the
  addendum), with a **50% signature-inference miss rate** on the four
  already read.
- The ~56-file `rt_string_len` figure predates the compilability-gate
  discovery. A *definition* census greps source and is not filtered by a
  compile-mode gate, so the figure should be unaffected — but this is
  reasoned, not re-measured.
- SIMD boundary-conversion strategy (convert once per call, not per
  comparison) remains **unmeasured**.
