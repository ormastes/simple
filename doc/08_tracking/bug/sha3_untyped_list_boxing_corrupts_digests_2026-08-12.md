# sha3.spl untyped-list boxing corrupts SHA-3 digests (same family as sha256_core, harder shape)

**Status:** OPEN — confirmed corrupt, partial fix attempted and reverted (did not fully resolve)
**Found:** 2026-08-12, during a sweep for other instances of the
`sha256_core_value_tagging_corrupts_live_digests_2026-08-11` defect family.
**Severity:** HIGH — `sha3_256_bytes`/`sha3_384_bytes`/`sha3_512_bytes` are
live public API and produce wrong digests.

## Confirmation

`sha3_256_bytes([97,98,99])` (FIPS "abc") on unmodified
`src/lib/common/crypto/sha3.spl`:

```
Expected (python hashlib.sha3_256): 58,152,93,167,79,226,37,178,4,92,23,45,107,211,144,189,133,95,8,110,62,157,82,91,70,191,226,69,17,67,21,50
Actual:                             208,20,0,0,0,0,0,0,1,32,207,148,205,4,0,0,17,32,207,148,205,4,0,0,33,32,207,148,205,4,0,0
```

The actual output has the repeating-byte-group shape (`207,148,205,4`) typical
of an unboxed/tagged pointer being read as raw bytes — same defect family as
`reference_native_dict_get_struct_corrupt_len_minus_one` /
`reference_list_get_returns_value_shifted_left_3` and the sha256_core
tagging bug.

## Attempted fix (reverted, did not resolve)

Applied the exact sha256_core recipe: retyped every `list` annotation in
`sha3.spl` to `[i64]` — all function signatures (`keccak_round_constants`,
`keccak_rotation_offsets`, `keccak_f1600`, `_bytes_to_lane_le`,
`_lane_to_bytes_le`, `_empty_state`, `_absorb_block`, `sha3_update`,
`sha3_finalize`, `sha3_final`, `sha3_256/384/512_bytes`,
`sha3_256/384/512_stream`), the `(list, list, i64, i64)` context tuple type
to `([i64], [i64], i64, i64)`, and internal `var s/c/d/b/out/tmp = []`
locals to explicit `var x: [i64] = []`, plus explicitly typing the
tuple-destructured `var state: [i64] = ctx[0]` / `var buffer: [i64] = ctx[1]`
locals in `sha3_update`/`sha3_finalize`.

Result: digest output changed but **remained wrong** with the same
tag-byte-repeat corruption signature, both before and after the retyping.
This differs from sha256_core, where the same recipe was sufficient.

## Suspected reason this is a harder case than sha256_core

`keccak_f1600` mutates its state via **bracket index assignment**
(`s[li] = s.get(li) ^ d.get(x)`, `b[_lane_idx(nx, ny)] = rotated`,
`s[0] = s.get(0) ^ rc.get(round_idx)`), not exclusively via `.push()`-built
fresh lists like sha256_core's message schedule. It's plausible the
element-type tracking that `[i64]` annotations buy on a `.push()`-built list
does not propagate the same way through `list[idx] = value` bracket-write,
which is documented elsewhere as a separate weak spot for native/class-field
array-value writes (see `.claude/rules/code-style.md`'s "Native-Codegen Dict
Pitfalls" note on bracket-write parity, a related but not identical class of
bug: `doc/08_tracking/bug/dict_set_bracket_write_parity_2026-08-07.md`).
Not confirmed further this session — flagging for the next investigator
rather than guessing further.

## Next steps for whoever picks this up

- Minimal repro should isolate `s[li] = ...` bracket-assignment specifically
  (not `.push()`), on both an untyped `list` and a `[i64]`-typed list, to see
  if bracket-write itself fails to preserve/decode the element type
  regardless of the declared type.
- If bracket-write is confirmed as the actual culprit, the fix is not
  file-local retyping but a compiler/runtime fix to `list[idx] = value`
  element-type propagation — out of scope for a `.spl`-level patch.
- Do not re-land the reverted retyping alone; it is necessary but
  insufficient here.

## Working tree state

The speculative retyping edits made while investigating this were reverted
before finishing this session — `src/lib/common/crypto/sha3.spl` is
unchanged from before this investigation, matching this file's own
"revert on failure" precedent set by the sha256_core doc.
