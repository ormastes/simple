# Dict reads against cache-loaded HIR modules fail through every Simple-level pattern (escalation)

Date: 2026-10-17 (p2_add bootstrap-sanity cycle 142)
Lane: runtime dict access vs cache-loaded modules — REQUIRES RUNTIME OWNER
Related: `rt_dict_values_aggregate_key_garbage_2026-10-17.md` (same campaign)

## Symptom

For p2_add's main-build module (loaded via `hir_cache_load_parsed_v1` →
generated-codec decode inside a transient scope, then promoted by the
recursive `rt_transient_heap_promote` walker), EVERY Simple-level read of
`module.functions` fails from HIR-phase-completion onward, while the module
SHELL (name, dict lengths) always reads fine and the monomorphization lane
(40.mono, same binary, dict from `ctx.hir_modules`) reads the same dicts
successfully.

Failed patterns (each verified by a `[race-trace]` probe receipt, cycles
132-142):
1. `functions.values()` → element words fault on first deref.
2. `keys()` + annotated key bind (`val k: SymbolId = ks[0]`) → bracket
   lookup nil (aggregate-key identity loss).
3. `keys()` + for-in element straight into the bracket → nil/empty.
4. Dict+key transport with ALL reads inside the codec pool
   (`hir_module_first_fn_name_in_v1`) → empty.
5. (cycle-142 probe, pending) generated-codec walk with
   `hc_order_symbol_id_keys_v1` ordering → verdict pending.

Working references:
- The generated codec walks the SHARD WORKER's freshly-lowered modules
  fine (`hir_module_has_rt_hal`, encode/decode digests — cycles 82-84).
- Mono's `collect_function_entry_v1` reads functions of the mono-passed
  modules fine (cycles 85-90+).
- `hir-final` shell receipts (`.name`, `.functions.len()`) always fine.

## Hypotheses for the runtime owner

H1. The generated DECODER builds dicts whose entry storage or key
    representation differs from lowering-lane dicts (e.g., keys stored
    un-canonicalized; the hash probe fails after the transient promote
    walker relocates/re-tags entries).
H2. The recursive promote walker relocates a dict's entries but not the
    key objects, so post-promotion key hashes mismatch the table.
H3. The dict read paths (`rt_dict_get`/`rt_dict_keys`/`rt_dict_values`)
    disagree about the dict KIND byte for decoder-built dicts in some
    states (as_dict succeeds for len, fails differently for iteration).

## Minimal repro

1. Build p2_add with the sharded lane (any cycle-133+ binary + this tree):
   `simple native-build --source src/compiler/bootstrap_admission/p2_add.spl
   --entry ...` with SIMPLE_SDN_RACE_TRACE=1.
2. The `hir-final-idx` receipt prints `first_fn_name=` (empty) while
   `functions=5`.
3. Compare against the mono lane's successful reads of the same dict.

## Cycle-148 final matrix (all patterns exhausted)

Every Simple-level read pattern fails on these dicts from every modern draw;
`hir_module_encode` (compiled in an early draw) succeeds:

| Pattern | Result |
|---------|--------|
| `.values()` element deref | fault / garbage words |
| `keys()` + annotated key bind + bracket | nil (identity loss) |
| `keys()` + for-in element straight into bracket | empty |
| in-pool dict+key, all reads in `hir_codec.spl` | empty |
| `hc_order_symbol_id_keys_v1` ordered walk | empty |
| fresh OUT-OF-SCOPE decode of the re-encoded blob | empty |
| while+index, `ks[i]` expression into bracket (`ks_len=5` prints) | empty |
| blob -> decode -> in-pool unwrap-bind -> while+index (all in one small fn) | empty |
| `hir_module_encode(modules[key])` | SUCCESS (3808 bytes, deterministic digest) |

## Disassembly fingerprint (cycle-148)

Both the working generated walk (`hc_enc_hir_module`, first functions-dict
`rt_index_get` at 0xf5b0a0) and a failing hand-written walk
(`hir_module_first_fn_name_wi_v1`, `rt_index_get` at 0xf70a08) prepare the
call IDENTICALLY: dict handle from `[reg, #48]`, key, `bl rt_index_get`.
The calls are the same; the DICT HANDLE VALUE differs. In the failing
function the handle derives from the function's 176-byte CONDITIONAL
PROLOGUE COPY LOOP (f708a8-f709c4: 24 words of
`ldr/csel tag-adjust/str`) — the prime suspect is that this copy loop
mangles word #48 (the functions-handle word) of the by-value module
parameter. The compiler owner should verify: does word 6 of the copied
struct equal the incoming parameter's word 6 at f709c8?

Bisect hint: encode's draw predates the campaign's stage2 rebuilds; a
compiler change between the two compilations altered the prologue-copy
codegen for large by-value struct params. The campaign can bisect which
stage2 commit introduced the corrupting copy loop by rebuilding
`hir_module_first_fn_name_wi_v1`-shaped probes against older compilers.

## Campaign-side state

- Compiler-side workarounds landed through cycle-140 (keys+index feeds,
  mono-shape getters, dict+key transports) — none reach a readable dict.
- The cycle-142 ordered-walk probe (`hir_module_first_fn_name_ordered_in_v1`)
  is the last Simple-level pattern; if it also returns empty, this document
  is the handoff.
