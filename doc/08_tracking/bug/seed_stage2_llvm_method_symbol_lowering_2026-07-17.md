# Seed stage-2 link failure: LLVM backend misses method-call→rt_* lowering

**Date:** 2026-07-17
**Severity:** critical (the redeploy wall — blocks self-hosted bootstrap stage 2)
**Status:** FIX IN REVIEW — final stage-2 relink evidence pending

## Symptom

Bootstrap stage 2 (`SIMPLE_BOOTSTRAP` forces the seed's LLVM llc path to
native-build `src/app/cli/bootstrap_main.spl`) fails at link with 67
deduplicated undefined symbols against `libsimple_native_all.a`.
Evidence log: `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`.

## Root cause (scout S60 + verified S63)

WRONG-NAME problem, not a missing-runtime problem:

- 40 of the 67 are literal method-call symbols (`str.substring`, `str.bytes`,
  ...) emitted by the seed's **LLVM backend**, which lacked part of the
  method-call→rt_* interception that the **Cranelift backend** has
  (`src/compiler_rust/compiler/src/codegen/instr/calls.rs` ~3162-3200).
  The runtime archive itself is complete (rt_* definitions present; verified
  via nm — 223K+ symbols).
- Residual classes: ~11 compiler-internal names leaking to link, ~13 runtime
  functions genuinely absent or differently named, 3 alloc/memory symbols.

## Fix policy (important precedent)

Only mappings **copied verbatim from the Cranelift table** or with verified
arity+semantics AND a proven-existing runtime symbol may be added to the LLVM
`runtime_func` map (`llvm/functions.rs`). An earlier fix attempt invented
aliases (`split_whitespace→rt_string_split` — arity mismatch;
`byte_at→rt_string_char_at` — byte-vs-char semantics; targets like
`rt_string_push_str`/`rt_to_hex` that do not exist in the runtime). Such
mappings convert loud link errors into silent miscompiles and were rejected in
review. Methods with no correct runtime target stay **unmapped (loud)**:
`str.lines`, `str.parse_int_radix`, `str.push_str`, `str.to_hex`, `str.byte_at`,
`str.split_whitespace`, `str.to_lowercase` — their long-term route is
a stdlib-compiled symbol (the existing `repeat → lib__common__string_core__str_repeat`
pattern) or earlier lowering.

The 2026-07-18 residual relink exposed three proven cases. `str.ord` and
`str.hash` now lower once in backend-neutral MIR to
`rt_string_char_code_at(receiver, 0)` and `rt_str_hash(receiver)` respectively;
focused MIR tests prevent either qualified name from reaching a backend.
`Dict.remove` maps in LLVM to the existing, arity-compatible
`rt_dict_remove` provider and has a focused IR-symbol regression. The same
relink also exposed an independent missing `impl MethodResolver:` owner in the
pure-Simple resolver; its instance methods had been parsed as nested functions,
leaving `MethodResolver.resolve_module` undefined at link.

## Verification protocol

1. Targeted cargo codegen tests (regression tests assert `bytes`/`chars` lower
   to `rt_string_bytes`/`rt_string_chars`, which exist at runtime.h:292-293).
2. Rebuild seed from fixed source; re-run ONLY the stage-2 native-build/link
   command from the log; report the actual residual undefined-symbol set.
   Expected: the 40 method-name symbols that have legitimate mappings drop;
   a residual set remains and is tracked here.

## Related

- `deployed_seed_test_runner_init_hang_2026-07-17.md` — stale seed at the
  release path; refreshed/self-hosted redeploy depends on this fix.
- `bootstrap_stage2_empty_mir_bodies_2026-07-05.md`,
  `selfhost_bootstrap_unresolved_symbols_2026-06-24.md` — earlier stage-2 walls.

---

# Residual-62 Classification (Lane S72)

**Date:** 2026-07-18  
**Baseline:** commit 192db6d7842 (wt_s9)  
**S60 Reference:** 67 original symbols from scout report

## Summary

After S63's fix (67→62), the residual 62 undefined symbols classify into four buckets with distinct root causes and fix strategies:

| Bucket | Category | Count | Root Cause | Fix Path |
|--------|----------|-------|-----------|----------|
| A | Method-call symbols | 35 | LLVM backend missing mappings (no lowering to lib-compiled symbols) | Add compiled-lib routing OR earlier lowering |
| B | Rust compiler internals | 11 | MIR stage captures Rust-internal names (struct/method symbols leaking from compile-time) | Resolve at HIR→MIR, prevent reference capture |
| C | Runtime functions (rt_*) | 13 | Genuinely absent from runtime OR conditionally compiled (missing EXTERN_DISPATCH) | Add stub, rename, or conditionally expose |
| D | Memory/allocation symbols | 3 | Likely LLVM-specific placeholders (dealloc', offset') | Filter from codegen OR resolve to existing malloc/free |
| **TOTAL** | | **62** | | |

---

## Bucket A: Residual Method-Call Symbols (35)

**Mapping:** 40 original - 5 fixed (bytes, chars, length, substring, [1 more TBD]) = 35 residual

### Residual list (inferred from S60 bucket A):

**Bare method names (2 residual):**
- `substring` (bare, if counted separately; may be same as str.substring)
- `split_whitespace` (bare)
- `Ok` (bare — unclear; check if this is a constructor, not a method)

**str.* method names (9 residual):**
- `str.byte_at`
- `str.lines`
- `str.ord`
- `str.parse_int_radix`
- `str.push_str`
- `str.split_whitespace`
- `str.to_lowercase`
- (2-3 more from S60's unlisted gap of ~24 symbols)

**Collection method names (1-2 residual):**
- `MutSlice.subslice`
- (f64.to_hex status TBD — may have been fixed with "to_hex → rt_to_hex" if such a runtime function exists)

### Analysis

**Source:** S60 verified these come from `common__sdn__value__`, `common__string_builder__`, `nogc_async_mut__binary_io__`, etc.

**Fix policy (from root-cause analysis):**
1. **Verified Cranelift mappings:** Only add mappings already in Cranelift (`src/compiler_rust/compiler/src/codegen/instr/calls.rs` ~3162-3200).
2. **Arity + semantics must match:** Avoid silent miscompiles (e.g., `split_whitespace→rt_string_split` has arity mismatch; `byte_at→rt_string_char_at` has byte-vs-char semantics).
3. **Compiled-lib pattern:** For methods with no direct rt_* match, route through stdlib-compiled symbol: `repeat → lib__common__string_core__str_repeat`. This is the long-term pattern.

**Highest-leverage fix:** Route unmappable methods to **compiled-lib symbols** via earlier lowering in the Cranelift/LLVM backend. Identify which 35 methods have existing stdlib implementations and add those as the canonical targets.

---

## Bucket B: Rust Compiler Internals (11)

### Symbols (from S60):
```
compiler_rust__lib__std__src__core__traits__Iterator.collect'
CopyPropagation.propagate_instruction'
CopyPropagation.propagate_operand'
CopyPropagation.propagate_terminator'
HirExpr.free_variables'
MirLowering.lower_inline_lambda_with_locals'
SpecializationKey.mangled_name'
ShbReader.read_full_interface'
TreeSitter.parse_* (9 variants: is_at_end, match_token, parse_bitfield_field_outline, ...)
val_kind'
```

### Analysis

**Pattern:** Names have `'` suffix and are Rust struct/method names (compile-time types being reified as runtime symbols).

**Root cause:** These are being captured as string literals in the MIR stage, likely as method/field names embedded in dynamic dispatch tables or reflection structures. The names should be resolved/lowered at HIR→MIR transition, not left for link-time.

**Verification points:**
- Grep `src/compiler_rust/compiler/src/codegen/instr/` for where `Iterator.collect'` or `CopyPropagation` names are emitted as symbols.
- Check `src/compiler_rust/compiler/src/codegen/dispatch.rs` for whether method-name capture is conditional on backend.
- Check MIR lowering for struct/trait method encoding.

**Fix strategy:** 
1. **Prevent capture:** Ensure HIR→MIR lowering resolves method names to vtable indices or direct function pointers, not string names.
2. **Filter at codegen:** If MIR still contains names, the LLVM backend should filter them rather than emit them as external symbols.
3. **Owner:** Rust seed (codegen) — this is not a runtime bug.

**Lowest priority for self-hosted path:** These require deep codegen refactoring. If stage-2 blocks, consider the Cranelift path (does it emit these symbols?).

---

## Bucket C: Runtime Functions (13)

### Symbols (from S60):
```
rt_dict_insert
rt_eprintln
rt_file_modified
rt_file_modified_time
rt_file_read
rt_host_gpu_active_backend_handle
rt_list_dir_recursive
rt_path_extension
rt_path_filename
rt_path_normalize
rt_sdn_parse
rt_string_contains
rt_smf_reader_open
rt_smf_reader_close
rt_smf_reader_read_header
rt_smf_reader_read_section
rt_smf_reader_read_string_table
rt_smf_reader_read_symbol_table
```

### Verification checklist

For each rt_* symbol, check:
1. **Definition exists in runtime:** `grep -r "rt_dict_insert\|rt_eprintln\|..." src/runtime/`
2. **Exported via EXTERN_DISPATCH:** Check if the symbol is listed in `src/runtime/sffi_dispatch.h` or the dynamic-dispatch registry (reference: CLAUDE.md memory note: "MCP-on-bootstrap FIXED: rt_string_bytes missing EXTERN_DISPATCH entry").
3. **Conditionally compiled:** Some rt_* functions may be gated by platform/feature flags (`#[cfg(...)]`) and missing from the archive during stage-2 native-build.
4. **Name mismatch:** Verify no underscores/casing mismatches between definition and reference.

### Fix strategy

1. **Existence check:** Confirm each rt_* is actually defined (or identify the correct name).
2. **EXTERN_DISPATCH:** If the symbol exists but is undefined at link, add to dispatch table.
3. **Conditional compilation:** If a runtime function is platform/feature-gated, either:
   - Rebuild the archive with the feature enabled, OR
   - Add a stub that returns an error/nil, OR
   - Gate the caller to not reference it at compile-time.
4. **Rename:** If the definition uses a different name (e.g., `dict_insert_internal`), update the mapping.

**Owner:** Runtime layer — these are missing definitions or dispatch misconfigurations.

---

## Bucket D: Memory/Allocation Symbols (3)

### Symbols (from S60):
```
dealloc'
offset'
(1 more TBD from gap)
```

### Analysis

**Pattern:** Likely LLVM-emitted placeholders for memory operations or compiler intrinsics.

**Possible sources:**
1. **LLVM intrinsics:** `llvm.memset.*`, `llvm.memcpy.*`, or backend-specific symbols.
2. **Custom allocator shims:** Codegen emitting references to `dealloc` or `offset` as if they were external functions.
3. **Cranelift vs. LLVM:** The Cranelift backend may handle these differently (resolving them to `rt_free` or similar), while LLVM leaves them unresolved.

**Fix strategy:**
1. **Identify source:** Find where `dealloc'` and `offset'` are emitted in `src/compiler_rust/compiler/src/codegen/llvm/`.
2. **Map or filter:** Either:
   - Add a mapping: `dealloc' → rt_free`, `offset' → rt_pointer_offset` (verify these exist in runtime).
   - OR filter them entirely if they're LLVM-internal intrinsics that should not leak to the link stage.
3. **Verify Cranelift:** Confirm Cranelift does NOT emit these, and if so, learn its strategy.

**Owner:** Rust seed (LLVM backend) — likely a codegen hygiene issue.

---

## Highest-Leverage Fixes (Top 3)

1. **Route bucket A (35 symbols) to compiled-lib symbols** (+35 symbols resolved)
   - **Leverage:** Eliminates 56% of residual undefined symbols in one pass.
   - **Effort:** Medium (requires identifying stdlib implementations and adding lowering).
   - **Owner:** Seed LLVM backend + stdlib mapping.
   - **Blocks:** None (once verified, can be landed independently).

2. **Fix bucket B (11 Rust internals) at HIR→MIR lowering** (+11 symbols resolved)
   - **Leverage:** Eliminates 18% of symbols; unblocks confidence in stage-2 codegen.
   - **Effort:** High (deep codegen refactoring).
   - **Owner:** Rust seed codegen.
   - **Blocks:** Full stage-2 reliability; considered lower priority for pure-Simple self-hosted path.

3. **Audit bucket C (13 rt_*) for existence and dispatch** (+13 symbols resolved)
   - **Leverage:** Eliminates 21% of symbols; likely quick wins on EXTERN_DISPATCH or naming.
   - **Effort:** Low (grep + dispatch config).
   - **Owner:** Runtime layer.
   - **Blocks:** If rt_* are actually missing definitions, requires runtime extension.
