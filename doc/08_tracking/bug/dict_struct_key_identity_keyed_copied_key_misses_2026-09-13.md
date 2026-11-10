# A Dict keyed by a struct is keyed by object identity, so a copied key silently misses
## Open 2026-09-16 — needs owner triage; re-confirmed LIVE 2026-11-11 (lane ne6) — per-lane measurement in the addendum below

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-8 while measuring site 8
  (`stage2_stage3_route_segv_mir_json_shadow_witness_2026-09-13.md`), which this defect caused.
- Severity: silent wrong answer. A lookup with a structurally-identical key returns nil, and
  callers that do not guard nil dereference it — site 8 was a SEGV in a Stage-2 compiler.

## The defect

For a heap key that is not a string, a boxed float or a boxed uint — i.e. for a **struct** —
the C bootstrap runtime hashes the RAW POINTER and compares by identity:

- `rt_core_dict_canon_key` returns the value verbatim (`src/runtime/runtime_native.c:9216`,
  `if (rt_core_is_heap(k)) return k;`).
- `rt_core_dict_hash` mixes `(uint64_t)k`, the pointer (`runtime_native.c:9232-9239`).
- `rt_native_eq` returns 0 for two distinct struct allocations: after the string / uint /
  float / special arms it requires a registered array or enum, and a struct is neither
  (`runtime_native.c:4030-4034`).

Hash and equality therefore AGREE — the dict is consistently identity-keyed for struct keys.
The defect is the interaction with struct **value semantics**: binding a struct to a local
copies it. Under native codegen the copy is explicit — the callee prologue is
`rt_alloc(<size>)` followed by a field-by-field copy, taken only when the incoming value
carries `TAG_HEAP` and a non-null pointer (see the site-8 record's disassembly). So

```
val k = keys[i]      # fresh allocation
d[k]                 # nil, even though keys[i] came out of d.keys()
```

is a miss, and nothing in the language or the runtime says so.

## Measured, one variable per run

Shared Rust seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
sha256 `3d120a6f9ab5704b...`. Probes under
`scratchpad/boot8/probe/{dictkey.spl,dictkey2.spl,dictkey3.spl,iso.spl,real_sort.spl}`.

| probe | result |
|---|---|
| `d[a]` with the inserted object | `direct=10` |
| `d[b]` where `b` is a structurally identical fresh struct | `copied=nil` |
| `val t = keys[0]; d[t]` | `viakeys=nil` |
| `for k in d.keys(): d[k]` (loop binding, no copy) | `for_keys_hits=2 of 2` |
| the same keys through a bubble sort that binds `val temporary = result[i]` | `sorted_hits=1 of 2` |
| swap via a one-element holder array (no struct local) | `a_hits=3 of 3` |
| sort an int permutation, rebuild with `result.push(keys[index])` | `b_hits=3 of 3`, order `2,5,9` |

**Lane caveat, stated rather than papered over.** The copy is lane-dependent. The SAME bubble
sort resolves 1 of 2 / 2 of 3 when it is a local function in a `simple run` script (JIT/native
codegen), and 20 of 20 when the identical algorithm is called through the
`compiler.driver.driver_types` import in the interpreter (`real_sort.spl`), which never
allocates the copy. A spec that asserts the miss therefore flips verdict with the lane it
runs in, which is why site 8's spec asserts the product's structure instead.

## Not fixed here, and why

Making struct keys structural would mean a deep hash plus a deep `rt_native_eq` arm in BOTH
runtimes (`src/runtime/runtime_native.c` and `src/compiler_rust/runtime/src/value/`), on the
hot path of every dict operation, and it would change the observable identity of every
existing struct-keyed dict. That is out of a bootstrap lane's budget and needs a decision on
which semantics the language wants. Site 8 was fixed at its call site instead: the sort no
longer copies its keys.

## Audit of the same shape elsewhere (2026-09-13, `src/**.spl`)

5,406 `val x = arr[i]` bindings exist, but the shape is only dangerous when the element is a
struct that is later used as a dict key. Filtering the files that sort with a struct
temporary AND mention a `[SymbolId]`/`[LocalId]`/`[HirSymbol]`/`[BlockId]` array leaves two:

- `src/compiler/80.driver/driver_types.spl` — the site-8 defect. FIXED.
- `src/compiler/50.mir/verification_ir.spl:200-206` — sorts the dict's VALUES
  (`functions.push(module.functions[symbol])`) and never re-looks-up by a copied key. Safe.

Every other struct-temporary sort found sorts `text` or ints (`driver_types.spl:356` sorts
`function.type_bindings.keys()`, which are text, and text keys hash structurally).

**That audit is narrower than the defect, and the gap is stated rather than implied.** It
covers only the SORT shape. A struct-typed **field read** copies too: the same candidate
binary shows an 8-word nil-guarded copy at `0x3677588`-`0x36775ec` whose result is re-tagged
`orr x9, x0, #1`, i.e. reading a struct field out of a struct hands back a fresh object. So

```
val k = func.symbol      # fresh allocation, not the object stored in the dict
module.functions[k]      # nil
```

misses natively for exactly the same reason, and that shape is **unaudited** — it is the most
likely form of a next site. Any audit that closes this bug has to cover struct field reads,
struct returns and struct arguments, not just array-element sorts.

## How to close this

Either give struct keys structural hashing + equality in both runtimes, or refuse them: make
a struct-keyed `Dict` a compile-time error unless the type opts in. Until then the language
guide needs the rule "never bind a struct dict key to a local before looking it up".


---

## Addendum 2026-11-11 (lane ne6, batch p3-ne6)

**Verdict: LIVE** — the copied/twin key still misses, per-lane state below.
The language-level decision this doc demands (structural hash+eq in both
runtimes, or compile-time refusal, or guide rule) has not landed; the defect
cannot be closed by a P3 traverse lane.

Measured on the refreshed seed (v1.0.0-rc.1, build-commit 0791c2b7f4a7),
`build/p3-ne6-probes/dictkey_probe*.spl`, `--mode=interpreter` (seed-smoke):

- `d[a]=10` with `a = Point(1,2)`, then `d[b]` for a separately constructed
  `Point(1,2)` → **nil** (`copied=nil`).
- Inserting both twins → `len=2`: the two structurally identical keys land in
  distinct buckets (identity-keyed).
- `d[keys()[0]]` (the bundled original object) → hits; `d[Point(1,2)]` inline
  fresh → nil.
- Text-form probes `d["Point{x=1,y=2}"]` / `d["Point{x=1, y=2}"]` both miss.

Per-lane source state at tip:

- **C runtime (`src/runtime/runtime_native.c:13252-13330`): UNCHANGED.**
  `rt_core_dict_canon_key` still returns a heap key verbatim (`:13275`), and
  `rt_core_dict_hash` still falls through to hashing the raw pointer for a heap
  non-float/non-uint (`:13316`). (Float and uint-box keys got value-hashing
  since this doc; structs did not.)
- **Rust native twin (`src/compiler_rust/runtime/src/value/dict.rs`): FIXED in
  source.** `hash_value` delegates to `sffi::equality::value_hash` and
  `keys_equal` to `rt_value_eq` (canonical structural hash/eq shared with
  `==`), with `dict_composite_key_tests::struct_key_via_variable_*` pinning it.
  The fix predates the seed build commit, so the JIT/native Rust-runtime lane
  carries it.
- **Seed interpreter: identity-keyed at runtime despite structural-looking tip
  source.** `compiler/src/value_impl.rs` `to_key_string()` has the canonical
  sorted-field `Value::Object` arm at tip (and at the seed's build commit), yet
  the running binary buckets struct twins separately. That is a
  seed-vs-source discrepancy on the interpreter lane — flagged here for the
  seedfix lanes; not root-caused further in this lane.

The "copied key silently misses" hazard is therefore still live on the
interpreter lane of the current seed and in the C runtime; the unaudited
shapes called out in this doc (struct field reads, struct returns/arguments as
lookup keys) remain unaudited.
