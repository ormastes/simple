# BUG-IT-10 — 50.mir builtin method table: holes on text / array / Result / numeric receivers

Date: 2026-10-10. Status: OPEN. Lane: stage2 intensive tests. release/1.0 @ b68c0c65708.
Spec: `test/01_unit/compiler/50.mir/builtin_method_table_holes_spec.spl` (`@tag:in-development`, one
example per method; the resolved families are in `builtin_method_table_sweep_spec.spl`).
Each hole fails closed with `unresolved method call: <name>`.

| receiver | unresolved in stage2 MIR | call sites in src/ (upper bound, compiler/app/lib) |
|---|---|---|
| text | `repeat` | 28 / 11 / 60 |
| array | `reversed`, `sorted`, `reduce`, `find`, `index_of` | sorted 28/2/3, reduce 1/4/3, find 223/304/138*, index_of 158/592/800* |
| Result | `map`, `map_err`, `ok` | map_err 0/7/0 (`unwrap_or` itself resolves: its two sweep diagnostics were on the results of the unresolved `map`/`map_err` calls) |
| i64 / f64 | `abs`, `min`, `max`, `floor`, `round` | abs 6/17/9, min 16/3/11, max 26/5/12, floor 0/4/8, round 0/1/12 |

`*` receiver-blind counts: `text.index_of` / `text.find` / `Option.unwrap_or` DO resolve, so the array
shares are smaller — but non-zero in the compiler itself (`sorted` 28x in src/compiler).
Resolved in the same sweep: text len/starts_with/ends_with/contains/split/join/trim/upper/lower/
replace/substring/index_of/char_at; array push/pop/contains/first/last/slice/map/filter/join/
is_empty; dict index-set/get/contains_key/keys/values/remove/len; Option unwrap_or/map/is_some/
is_none/.?/unwrap; Result unwrap_or/is_ok/is_err; numeric to_f64/to_i64/to_text, `text.to_i64`.

Scope note: under `SIMPLE_BOOTSTRAP=1` MIR lowering is skipped for non-entry modules, so these bite
the entry module today and everything in a stage4 / non-boot build. Ask: wire the missing names in
the MIR builtin dispatch, prioritised by the compiler's own use: `sorted`, `repeat`, numeric
`min/max/abs`, array `find`. When one is wired, move its example back to the
sweep's family example.
