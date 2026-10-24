# Packed binary AST v1 — pointer-free, mmap-in-place flat-pool blob

**Status:** design review for the packed blob the scheduling lane is starting
(2026-10-24, `release/1.0.0` @ `49308eebea4`). Implements rule 6 of
[`src_based_tldr_build_v1.md`](src_based_tldr_build_v1.md) ("the parse cache
entry IS the AST: final immutable binary, used in place; a replay log is not a
cache"). Line numbers are at `49308eebea4`.

**User rules this doc enforces:** no pointers on disk (offsets/indices and
stable module-key/decl-id refs only); lazy async cross-module pointers saved
**unfilled**; set-once fields; one packed contiguous blob per source file
(header, section table, little-endian node arrays, interned string pool) holding
AST **and** TLDR, keyed by content key + compiler version; mmap-aligned.

## 0. What exists today (the thing being replaced)

- Pools: 167 array-typed `var`/`pub var` globals across
  `src/compiler/10.frontend/core/{_Ast/decl_nodes.spl, _AstExpr/nodes.spl,
  ast_stmt.spl, types.spl}`; the per-parse set is defined by the reset
  functions, not by file membership
  (`scripts/check/check-flat-ast-codec-complete.shs:84-97`, oracle
  `RESET_FNS`).
- Codec: `core/flat_pool_codec.spl` — **text**, line-oriented, escaped
  (`:22-40`), version `spl-flatpool-v8-a5-refusal` (`:56`); 166 `enc_*` calls
  across `flat_decl_pools_dump` (`decl_nodes.spl:1657`),
  `flat_expr_pools_dump` (`nodes.spl:1047`), `flat_stmt_pools_dump`
  (`ast_stmt.spl:715`), `flat_type_pools_dump` (`types.spl:1783`) plus one
  scalar (`current_scope_depth`).
- Hit path: `_FlatAstBridge/module_assembly.spl:1444`
  `build_module_from_flat_pool_blob` → `reset_all_pools()` →
  `parser_init_with_path` → `flat_pools_restore_all` (`:1336`, version check
  `:1340`) → `flat_ast_to_module` (bridge) → sanitize dry-run re-encode
  (`:1509-1512`). Capture globals `_fab_capture_pools`, `_fab_captured_blob`,
  `_fab_captured_paths`, `_fab_capture_arm_tag` (`:1395-1428`).
- Keys: private cache = `xxh3_128_text(content)` + header
  `FRONTEND_CACHE_ENTRY_VERSION FLAT_POOL_CODEC_VERSION scope`
  (`frontend_parse_cache.spl:110-136`); shared CAS = sha256 payload digest,
  no-replace (`frontend_shared_parse_cas_v1.spl:5,48`).
- Consumer: everything downstream reads `ParserModule`
  (`parser_types.spl:24`, heap structs + `Dict<text, …>`), never the pools.

Why it is non-compliant: every hit decodes text into pools, rebuilds heap
structs, and re-encodes for validation — a replay, not an in-place AST. The
pools also carry process-local state (below) that is serialised today.

## 1. Field inventory

Legend — **K** keep as-is (plain value or intra-blob index); **I** convert to
offset/count into a flat array (or to an index into the string pool);
**X** convert to a stable cross-file ref `(module key, decl id)` saved
**unfilled**; **C** CLEAR before save (never written; reader re-derives or
never needs it); **R** recompute on load (derived from other sections).
All `[text]` become **I** (string-pool index) unless marked X or C; all
`[[i64]]`/`[[text]]` become **I** (offset+count into a flat child array).

### 1.1 Declarations — `core/_Ast/decl_nodes.spl` (dump `:1657-1743`)

| Pool (line) | Type | Disposition | Reason |
|---|---|---|---|
| `decl_tag :262`, `decl_span :263`, `decl_ret_type :268`, `decl_is_* :287-325` (async, comptime, lazy, gpu_kernel, rt_hal_flags, simd, packed, trait, hardware, value_type), `decl_flatten_struct_output :317`, `decl_unroll_factor :322`, `decl_pipeline_ii :323`, `decl_memory_banks :324` | `[i64]` | **K** | plain scalars / indices into span and type pools |
| `decl_name :264`, `decl_visibility :286`, `decl_asm_placement :295`, `decl_gpu_target_text :296`, `decl_gpu_target_arg_name_text :297`, `decl_gpu_backends_text :298`, `decl_impl_trait :307`, `decl_param_mut_text :336`, `decl_param_default_text :344` | `[text]` | **I** | string-pool index |
| `decl_params :265`, `decl_param_types :267`, `decl_body_stmts :269`, `decl_field_types :282`, `decl_field_defaults :283`, `decl_field_bits :284`, `decl_vhdl_generic_args :316`, `elif_body :1432`, `elif_else :1433`, `arm_body :1363` | `[[i64]]` | **I** | flat child array + (offset,count) |
| `decl_param_names :266`, `decl_field_names :281`, `decl_type_params :289`, `decl_type_param_constraint_mode :291`, `decl_derives :301`, `decl_clocked_args :315` | `[[text]]` | **I** | (offset,count) into a flat string-index array |
| `decl_type_param_constraints :290` | `[[[text]]]` | **I** | two-level (offset,count) |
| `decl_imports :285` | `[[text]]` | **X** | each import is a cross-module reference: store `(module key = logical path digest, decl id or 0)` **unfilled**; the resolved import target is a set-once pointer in RAM only |
| `decl_body_stmts_flat :280`, `arm_body_flat :1370` | `[text]` | **C** (drop from blob) | text twins of `[[i64]]` that exist only because the native seed erased nested lists to a boxed handle (`:270-280`, `:1363-1370`); the flat (offset,count) child array **is** the fix, so the twin is redundant on disk — the reader derives it if the seed still needs it (**R**) |
| `arm_pattern :1361`, `arm_guard :1362`, `elif_cond :1431` | `[i64]` | **K** | expr indices |
| `arm_binding :1371`, `arm_rationale :1372` | `[text]` | **I** | |
| `module_decls :1475` | `[i64]` | **K** | decl indices (module roots) |
| `module_decl_slots :1476` | `[i64]` | **R** | derived slot table |
| `module_path_slot :1474` | `[text]` | **X**→ header | replace with the **logical** module key in the header; never store an absolute/host path |
| `ast_decl_count_slot :93`, `ast_module_decl_count_slot :94` | `[i64]` | **R** | equals section element count |
| `ast_decl_mirror_high_slot :51`, `ast_module_decl_mirror_high_slot :52` | `[i64]` | **C** | high-water marks of the interpreter **environment mirror** (`:44-52`): process-local |
| `lexer_state_core_pos_slot :1577`, `lexer_state_core_line_slot :1578` | `[text]` | **C** | lexer cursor state; meaningless post-parse |
| `decl_empty_i64 :345`, `decl_empty_text :346`, `decl_empty_text_lists :347` | sentinels | **C** | immutable empty sentinels (script notes them as non-state) |

### 1.2 Expressions — `core/_AstExpr/nodes.spl` (dump `:1047-1089`)

| Pool (line) | Type | Disposition | Reason |
|---|---|---|---|
| `expr_tag :93`, `expr_span :94`, `expr_i_val :95`, `expr_left :98`, `expr_right :99`, `expr_extra :100` | `[i64]` | **K** | values / expr, span, type indices (`expr_extra` holds a type handle into the type arena, `:102` — an index, not a pointer) |
| `expr_f_val :96` | `[text]` | **K**→ **I** or 8-byte LE f64 | text today for determinism; store canonical shortest-round-trip text in the string pool, or the IEEE bits — pick one, never both |
| `expr_s_val :97` | `[text]` | **I** | |
| `expr_args :101`, `expr_call_type_args :103`, `expr_stmts :105`, `expr_asm_outputs :109` | `[[i64]]` | **I** | |
| `expr_arg_names :104`, `expr_asm_kinds :106`, `expr_asm_locations :107`, `expr_asm_clobbers :108` | `[[text]]` | **I** | |
| `asm_arm_archs :834`, `asm_arm_ver_ops :838` | `[[text]]` | **I** | |
| `asm_arm_os :835`, `asm_arm_abi :836`, `asm_arm_backend :837`, `asm_arm_asm_text :840`, `asm_arm_error_msg :842` | `[text]` | **I** | |
| `asm_arm_ver_vals :839` | `[[i64]]` | **I** | |
| `asm_arm_is_compile_error :841`, `asm_arm_is_wildcard :843` | `[bool]` | **K** (u8 / bitset) | |
| `expr_count_slot :112` | `[i64]` | **R** | = element count |
| `ast_gen_slot :124`, `ast_gen_last_report_slot :125` | `[i64]` | **C** | **arena generation counter** (`:117-125`): monotonic diagnostic epoch; restoring it rewinds the generation guard — same class as the excluded `par_initialization_generation_v1` (`check-flat-ast-codec-complete.shs:78-83`) |
| `expr_env_mirror_high_slot :132` | `[i64]` | **C** | environment-mirror high-water mark (`:126-132`), process-local |
| `expr_empty_i64 :110`, `expr_empty_text :111` | sentinels | **C** | |

### 1.3 Statements — `core/ast_stmt.spl` (dump `:715-741`)

| Pool (line) | Type | Disposition | Reason |
|---|---|---|---|
| `stmt_tag :48`, `stmt_span :49`, `stmt_expr :50`, `stmt_type_tag :52`, `stmt_if_single_else :57` | `[i64]` | **K** | |
| `stmt_name :51` | `[text]` | **I** | |
| `stmt_body :53` | `[[i64]]` | **I** | already mirrored by `stmt_body_offsets/counts/flat :54-56` — keep **only** the flat triple on disk (model for every other `[[i64]]`) |
| `stmt_body_offsets :54`, `stmt_body_counts :55`, `stmt_body_flat :56` | `[i64]` | **K** | the canonical (offset,count,flat) form |
| `stmt_gpu_grid_exprs :534`, `stmt_gpu_block_exprs :535` | `[[i64]]` | **I** | |
| `stmt_if_val_marker :59` | `[bool]` | **K** (bitset) | |
| `stmt_count_slot :60` | `[i64]` | **R** | |
| `stmt_env_mirror_high_slot :68` | `[i64]` | **C** | environment mirror, process-local |
| `stmt_empty_i64 :58` | sentinel | **C** | |

### 1.4 Types, spans, tokens, symbols — `core/types.spl` (dump `:1783-1946`)

| Pool (line) | Type | Disposition | Reason |
|---|---|---|---|
| `span_pool_start/end/line/col :99-102` | `[i64]` | **K** (u32 each) | byte/line offsets into the content-keyed source; the `file` of a `Span` is supplied by the reader from the header's module key, never stored per span |
| `tok_pool_kind/span/text :149-151` | tokens | **C** | lexer arena; **zero** readers in `_FlatAstBridge`, desugar or the parser after parse (grep 2026-10-24); re-tokenising is never needed for a cached module |
| `sym_names/types/depths/decl_ids/mutable :173-177`, `scope_starts :216`, scalar `current_scope_depth :217` | symbol table / scope stack | **C** | parser-session scope state ("symbols after that index are hidden", `:210-217`); zero post-parse readers; today it is serialised and even the scalar is carried explicitly (`check-flat-ast-codec-complete.shs:51-56`) — drop |
| `named_type_names :758`, `custom_primitive_names :767`, `newunit_names/suffixes :923-924`, `fn_sig_names :1057`, `generic_param_names/contexts :1102-1103`, `named_generic_instance_bases :1353`, `refinement_predicates :1216` | `[text]` | **I** | |
| `named_type_arguments :759`, `named_type_field_types :762`, `fn_sig_param_types :1059`, `union_type_members :1134`, `tuple_type_elem_tags :1175`, `intersection_type_members :1195`, `named_generic_instance_args :1354`, `function_param_tags :1561` | `[[i64]]` | **I** | |
| `named_type_field_names :761`, `fn_sig_param_names :1058` | `[[text]]` | **I** | |
| all `*_inner_tags`, `*_mutable_flags`, `*_elem_tags`, `dict_type_keys/values`, `result_type_ok/err`, `refinement_base_types`, `fn_sig_ret_types`, `fn_sig_is_extern`, `function_ret_tags`, `newunit_underlying_type_tags`, `custom_primitive_underlying_type_tags` (`:1215-1562`) | `[i64]` type tags | **K** | tags encode (kind, index) into sibling type pools — intra-blob indices |
| `named_type_layout_owners :760` | `[i64]` | **K** if it is a decl index; **X** if it can name a decl of another module — the registry comment (`:750-760`) does not say; the generator check (§5) must assert which |
| `custom_primitive_symbol_ids :769` | `[i64]` | **K** if decl index, else **C**+**R** — "symbol id" must not be a `sym_*` table index (that table is cleared); verify |
| `generic_param_ids :1104`, `named_generic_instance_ids :1352` | `[i64]` | **K** only if minted as dense per-parse indices; if they are session counters (minted across files in one process), they are **C** and re-minted on load (**R**) in blob order |

### 1.5 Not in the pools but serialised or needed

| Item | Disposition |
|---|---|
| `FLAT_POOL_CODEC_VERSION` first line (`module_assembly.spl:1318`) | → header `schema_version` |
| `SIMPLE_BOOTSTRAP_LEX_SOURCE/_PATH` env round-trip on hit (`:1460-1487`) | **C** — the in-place reader never touches process env; slices come from the string pool |
| `_fab_capture_*` globals (`:1395-1428`) | **C** — replaced by a pure `encode(pools) -> bytes` with no arm/take state |
| sanitize dry-run re-encode (`:1509-1512`) | removed — replaced by §4 validation |
| post-desugar invariant ("the blob is post-desugar", `:1468`) | header flag `desugared=1`; a reader that needs pre-desugar form must miss |
| TLDR companion (`cache/module_artifacts_v1.spl`, header `simple-tldr-companion: 4`) | co-located sections (§2.5); the `.tldr` file stays a *view* |

## 2. Packing layout

All integers little-endian. File offset 0 is 64-byte aligned by construction;
every section starts at a 64-byte boundary (one cache line; 8-byte arrays
trivially aligned; pages are 4 KiB multiples of 64).

### 2.1 Header (fixed 128 bytes)

| off | size | field | notes |
|---|---|---|---|
| 0 | 8 | magic | `"SPLAST\0\1"` |
| 8 | 4 | `schema_version` | u32, replaces `FLAT_POOL_CODEC_VERSION`; bump on any pool/field change |
| 12 | 4 | `header_len` | 128 |
| 16 | 16 | `content_key` | xxh3_128 of the source bytes (same as `frontend_parse_cache_key`) |
| 32 | 32 | `compiler_identity` | sha256 of the producer bundle (`native_build_cache_scope_key` producer identity / `compiler_fingerprint`) |
| 64 | 16 | `module_key` | xxh3_128 of the **logical** path (`frontend_shared_parse_logical_path_v1`) — the stable cross-file module id |
| 80 | 4 | `flags` | bit0 desugared, bit1 has_tldr, bit2 strings_utf8_validated, bit3 target_dependent |
| 84 | 4 | `section_count` | |
| 88 | 8 | `total_len` | whole blob, for bounds |
| 96 | 16 | `body_digest` | xxh3_128 over bytes `[128, total_len)` |
| 112 | 16 | reserved | zero |

Endianness is fixed LE; alignment is fixed 64; neither is a field (a reader
on a BE host byte-swaps on read, which the validation step (§4) handles by
checking the magic's byte order).

### 2.2 Section table (immediately after header, 32 bytes/entry)

| field | size | notes |
|---|---|---|
| `id` | u32 | enumerated below; unknown ids ⇒ fail closed (§4) |
| `elem_kind` | u8 | 1 = i64, 2 = u32, 3 = u8/bitset, 4 = str_index(u32), 5 = (offset,count) pair(u32,u32), 6 = bytes |
| `flags` | u8 | bit0 required, bit1 varint-compressed (only where §2.6 measured) |
| pad | u16 | |
| `offset` | u64 | from blob start, 64-aligned |
| `len` | u64 | bytes |
| `digest` | 8 | xxh3_64 of the section bytes |

Entries sorted by `id`. Section ids: `0x01xx` decl pools, `0x02xx` expr,
`0x03xx` stmt, `0x04xx` type/span, `0x05xx` string pool, `0x06xx` child flat
arrays, `0x07xx` cross-module refs, `0x08xx` TLDR, `0x0900` set-once field
map. One id per pool in §1 (K/I/X); no id for C/R pools.

### 2.3 Node arrays

- One section per pool; fixed-width elements; length = `len / width`, and the
  decl/expr/stmt/span counts **are** those lengths (the `*_count_slot` pools
  are gone).
- Indices into sibling pools are `u32` (`0xFFFF_FFFF` = none). i64 value
  pools (`expr_i_val`, type tags) stay 8 bytes.
- `[[i64]]`/`[[text]]` pools become a `(offset,count)` pair array (kind 5)
  plus one shared **child flat array** per element kind (`0x0601` i64 children,
  `0x0602` str_index children). `stmt_body_offsets/counts/flat` is already this
  shape and is the model.
- Booleans are bitsets (kind 3) padded to 8 bytes.
- **No varint by default.** Varint is admitted per section only after a
  measured size win on the bootstrap closure and only for child flat arrays
  (random access into node arrays must stay O(1)).

### 2.4 String pool (`0x0501` offsets `u32[n+1]`, `0x0502` bytes)

- Every distinct `text` value stored once; sorted by (byte length, bytes) so
  the pool and its indices are canonical (§3). `str_index` is a `u32` into the
  offsets array; `0xFFFF_FFFF` = none. Bytes are raw UTF-8 with no escaping
  (the text codec's escape rules at `flat_pool_codec.spl:30-36` exist only
  because it is line-oriented).
- Source slices the bridge needs are stored as strings here; the reader never
  re-opens the source.

### 2.5 TLDR sections (co-located, `0x08xx`)

- `0x0801` public facts = the `FrozenPublicFactV1` rows that
  `module_public_summary_facts_v1.spl` produces (kind-tagged, decl index,
  name str_index, canonical-bytes str_index); `0x0802` generic bodies,
  `0x0803` inline bodies as (decl index) lists; `0x0804` SIF text str_index;
  `0x0805` rendered companion text (optional, so `simple tldr --out` is a copy
  of a section, not a second producer).
- A TLDR-only consumer maps the blob and reads `0x08xx` + the string pool; it
  never touches the node arrays (forward-declaration semantics).

### 2.6 Set-once / empty fields

- Any field that may be unset on disk uses the **sentinel** `0xFFFF_FFFF`
  (u32 index kinds) or `i64::MIN` (i64 value kinds). The blob never stores a
  filled lazy value.
- Section `0x0900` is the **set-once field map**: for each set-once-capable
  (section id, element) class, a bitset of which elements are *allowed* to be
  filled at runtime. The RAM view allocates a parallel side array for those
  elements; the mmapped bytes are never written (map `PROT_READ`).

### 2.7 Lazy cross-module pointers (`0x0701`)

| field | size | notes |
|---|---|---|
| `module_key` | 16 | xxh3_128 of the target's logical path |
| `decl_id` | u32 | stable decl id in the target module = that module's decl index **in its own blob**, valid only together with `target_content_key` |
| `target_content_key` | 16 | content key of the target source the reference was resolved against at parse time, or zero when unresolved (always zero in v1: imports are not resolved by the parser) |
| `name` | u32 str_index | the imported symbol text, for re-resolution |
| reserved | 12 | |

`decl_imports` entries become indices into this table. The RAM-side pointer is
a set-once slot filled through the reader's single-flight table
(`src_based_tldr_build_v1.md` §6–§7); it is never serialised.

## 3. Determinism

Identical source bytes ⇒ byte-identical blob on any host/process:

1. **No hash-map iteration anywhere in encode.** `ParserModule.functions` is a
   `Dict` (`parser_types.spl:30`) — the encoder reads the **pools**, which are
   append-ordered by the parser, not the module struct.
2. **Pool order = parse order**, which is a pure function of the source
   (the parser is single-threaded over one file; `expr_alloc`/`stmt_alloc`/
   `decl_alloc` append). Any id that is minted from a **process** counter
   (`ast_gen_slot`, `par_initialization_generation_v1`, env-mirror marks, and
   possibly `generic_param_ids`/`named_generic_instance_ids`) is excluded (C)
   or re-minted on load in blob order (R).
3. **String pool sorted** by (length, bytes); indices are therefore canonical.
4. **Sections sorted by id**; padding bytes are zero; reserved fields zero.
5. **No addresses, pids, timestamps, hostnames, absolute paths.** The only
   path-derived field is `module_key`, computed from the logical path.
6. **No environment in the encoding.** `SIMPLE_CAPTURE_WRITE_CHECK`-level
   differences today make a hit a miss (`module_assembly.spl:1466-1472`); in v1
   the check level is part of `compiler_identity` or the flag word, never an
   implicit input.
7. **Floats** (`expr_f_val`) have one canonical representation (§1.2).
8. **Target-dependent parses** (conditional `@when`, target preprocessing) set
   `flags.target_dependent` and fold the target identity into
   `compiler_identity` — the shared CAS already keys on "target preprocessing
   identity" (`frontend_shared_parse_cas_v1.spl:3-4`).

The acceptance test is two processes on two hosts producing `cmp`-equal blobs
for the whole bootstrap closure (§5).

## 4. Validation on mmap load (fail closed, O(sections) + one body hash)

| Step | Check | On failure |
|---|---|---|
| 1 | file length ≥ 128; magic bytes exact (also detects byte order) | miss |
| 2 | `schema_version` == reader's; `compiler_identity` == reader's producer identity; `content_key` == key the caller asked for | miss (loud "version mismatch" in the log, as the private cache does today) |
| 3 | `header_len + 32·section_count ≤ total_len == file length` | miss |
| 4 | each section: `offset % 64 == 0`, `offset + len ≤ total_len`, sections non-overlapping and sorted, `len % width == 0` for its kind | miss |
| 5 | `body_digest` over `[128,total_len)` (one xxh3_128 pass; ~GB/s) **or**, when `SIMPLE_AST_VERIFY=sections`, per-section digests lazily on first touch | miss |
| 6 | unknown `id` with `required` set ⇒ miss; unknown optional ⇒ ignore; **missing** required id ⇒ miss | miss |
| 7 | **index bounds**: every `u32` index in a node array < target section length, every `(offset,count)` within its child array, every `str_index` < string count. Done once at load in one linear pass over index-kind sections (branch-free compare) — this is the replacement for today's sanitize re-encode and is what makes a torn/foreign blob a miss instead of a SIGSEGV (`module_assembly.spl:1493-1512`, bug `stage2_mir_shard_flat_pool_text_len_minus1_2026-10-22`) | miss |
| 8 | string pool: offsets monotonic, last offset == bytes length, `flags.strings_utf8_validated` set by the producer (reader trusts it after digest) | miss |
| 9 | `flags.desugared` matches what the caller needs | miss |

Cost target: steps 1–6 are a few hundred bytes of reads; step 5 is one hash
of the blob; step 7 is one pass over the index sections. All of it is
read-only on a `PROT_READ` mapping and allocates nothing. "Miss" means the
caller parses; the blob is never patched. A blob that fails step 5 or 7 is
additionally **quarantined** (renamed to `trash/`, as the AOP formal design's
GC does) so it is not re-validated on every request.

## 5. Risks and required specs

### Risks

| Risk | Why it is real here | Mitigation |
|---|---|---|
| **Silent miscompile from a missed field** | a pool not encoded "comes back EMPTY after a restore, which does not crash" (`check-flat-ast-codec-complete.shs:7-9`); a 151/151 false green already happened (`:84-88`) | keep the reset-function oracle; extend it to emit the §1 disposition table and fail when a pool has no disposition (spec 4) |
| **Clearing a field that is actually read** | `tok_pool_*`, `sym_*`, `scope_starts` have zero bridge/desugar readers by grep, but a reader could exist behind a helper | spec 1 (whole-closure byte round-trip through the **in-place reader**, not through a re-encode) catches any consumer that observes the cleared value |
| **Session-minted ids** (`generic_param_ids`, `named_generic_instance_ids`, `custom_primitive_symbol_ids`, `named_type_layout_owners`) | if minted across files in one process they differ between a sharded and an unsharded build and between hosts | spec 3 (two-process round trip) + determinism rule 2; decide K vs R per pool before the first producer lands |
| **Interning tables** | the interpreter's `intern.spl:21-29` tables and the env mirror are process state; a `text` pool must never hold an intern **id** | string pool stores bytes only; spec 2 scans for small-integer-looking values in str_index columns |
| **Heap addresses leaking as i64** | the seed erases nested lists to "a boxed i64 handle" (`decl_nodes.spl:1365`) — a handle is an address | spec 2: live-heap-address scan of every i64 section against the process's heap ranges at encode time |
| **Cross-host** | shared CAS admits only "the exact target-receipted parser input" (`frontend_shared_parse_cas_v1.spl:2`) | `compiler_identity` + `flags.target_dependent` in the key; no host path, no locale-dependent float text |
| **Reader still rebuilds `ParserModule`** | HIR consumes heap structs (`parser_types.spl:24`); if the bridge stays, the blob is still a replay | the in-place **view** layer (accessors over the mapped arrays) must be the first consumer; the bridge is allowed only as a temporary adapter behind a flag, and spec 1 measures a hit as map + validate only |
| **Writable mapping** | a set-once fill written into the mapped page corrupts every other process's view | `PROT_READ`; set-once lives in side arrays (§2.6) |

### Required specs (SSpec, `test/01_unit/compiler/frontend/packed_ast/`)

1. **Whole-closure byte round-trip** — for every file of the bootstrap closure:
   parse → encode → mmap+validate → in-place view; compare the view against
   the fresh parse field-by-field (tags, indices, strings, spans) and HIR
   output byte-for-byte. No re-encode on the hit side.
2. **Live-heap-address scan** — at encode time, every i64 in every section is
   checked against `[heap_lo, heap_hi)` and the transient-scope arena ranges;
   any hit fails the encode (`FAIL — address-like value in <section>[<i>]`).
   Plus: no `str_index` column contains a value ≥ string count (an intern id).
3. **Two-process / two-host round trip** — encode the same source in two
   separate processes (and once sharded `--parse-shard=i/n`, once not) and on
   the Linux and Windows hosts; blobs must be `cmp`-equal; then load each blob
   in the other process and run spec 1's comparison.
4. **Field-coverage generator check** — extend
   `check-flat-ast-codec-complete.shs`: derive the pool set from the reset
   oracle as today, then require every pool to appear exactly once in the §1
   disposition table (K/I/X/C/R) **and** every K/I/X pool to have a section
   id in the producer; a new pool with no disposition is a FAIL, a C pool
   that the producer encodes is a FAIL, and a stale disposition row is a FAIL.
   Verdict line `PASS — <n> pool(s) checked, <k> encoded, <c> cleared`;
   0 pools ⇒ ERROR.
5. **Fail-closed validation fixtures** — truncated file, flipped body byte,
   out-of-range index, overlapping sections, unknown required section, wrong
   `compiler_identity`, misaligned offset: each must be a miss with a reason,
   never a crash; cost of a validated hit on the largest closure file is
   recorded.

## 6. Clear / convert summary

| Disposition | Pools |
|---|---|
| **CLEAR** (never on disk) | `ast_gen_slot`, `ast_gen_last_report_slot`, `expr_env_mirror_high_slot`, `stmt_env_mirror_high_slot`, `ast_decl_mirror_high_slot`, `ast_module_decl_mirror_high_slot`, `lexer_state_core_pos_slot`, `lexer_state_core_line_slot`, `tok_pool_kind/span/text`, `sym_names/types/depths/decl_ids/mutable`, `scope_starts`, `current_scope_depth`, `decl_body_stmts_flat`, `arm_body_flat`, all `*_empty_*` sentinels, `_fab_capture_*`, env round-trip |
| **Recompute** | `*_count_slot` (= lengths), `module_decl_slots`, text twins if the seed still needs them, any session-minted id pools re-minted in blob order |
| **Cross-file ref (unfilled)** | `decl_imports` → `0x0701` table; `module_path_slot` → header `module_key`; `named_type_layout_owners` if it can cross modules |
| **Index/offset** | every `[text]` → str_index; every `[[i64]]`/`[[text]]`/`[[[text]]]` → (offset,count) + child flat array |
| **Keep** | all scalar `[i64]`/`[bool]` node fields, span pools (as u32), type tags |
