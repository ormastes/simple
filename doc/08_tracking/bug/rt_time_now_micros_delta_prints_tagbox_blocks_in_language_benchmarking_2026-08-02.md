# `rt_time_now_micros()` deltas print as tagbox garbage — in-language microbenchmarking is unusable

- Status: OPEN
- Found: 2026-08-02, while A/B-measuring a CPU-lane hot-path fix
- Binary: `bin/release/x86_64-unknown-linux-gnu/simple` (enum-probe = 0, i.e. the
  **Rust seed**) via `run <file>.spl`
- Related family: `native_to_i64_nil_coalesce_print_tagbox_leak_2026-07-20.md`,
  `native_bool_array_element_interpolation_special_garbage_2026-07-17.md`,
  `f64_integral_to_text_drops_fraction_2026-07-25.md`

## Symptom (PROVED, reproduced 5/5 runs)

A timing delta built from two `rt_time_now_micros()` reads and interpolated into
a string does not print as an integer. Across five identical runs of one program
the SAME expression printed in four different encodings:

```
per_node_us=<value:0x16c46>      hoisted_us=<special:18>
per_node_us=0.0000...033063      hoisted_us=<value:0x8e>
per_node_us=<value:0x10abc>      hoisted_us=<invalid-heap:0xa1>
per_node_us=<special:10228>      hoisted_us=0.0000...075
per_node_us=<special:9774>       hoisted_us=0.0000...075
```

Shape of the program:

```
val a0 = rt_time_now_micros()
... loop ...
val a1 = rt_time_now_micros()
print "per_node_us={a1 - a0}"
```

The float form is a denormal printed with ~320 leading zeros — the same
"integral value reinterpreted as f64" signature as the `f64_integral_to_text`
bug. `<invalid-heap:0xa1>` is the alarming one: a small integer is being treated
as a heap pointer.

## Why it matters beyond cosmetics

1. **It silently produces a WRONG NUMBER, not an error.** `<value:0x16c46>` and
   `<special:9774>` are both plausible-looking microsecond counts. A perf lane
   that quoted either would report a fabricated measurement and exit 0.
2. **The encoding is not stable across runs of the same binary on the same
   input**, so a single run cannot even be sanity-checked against a second one.
3. **It blocks the repo's own perf standard.** Verifying work with warm startup
   time and request latency is required by `.claude/rules/code-style.md`, and
   the natural way to do that from Simple is exactly this pattern.

## Workaround in use (not a fix)

Measure **externally** — one process per arm, `/usr/bin/time -f "%e %M"` for
elapsed seconds and max RSS, arms alternated within one window and repeated for
a variance estimate. This works but cannot time a region *inside* a program, so
it forces a whole benchmark process per arm and cannot isolate a hot region of a
larger run.

## Not yet established

- Whether the interpreter and the self-hosted bootstrap binary share the defect.
  Only the Rust seed was exercised. Do not assume the seed's behaviour
  generalises — per `reference_neither_engine_trustworthy`, each engine is
  silently wrong in different ways, so this needs an explicit per-engine check
  before anyone claims it is seed-only.
- Whether the corruption is in `rt_time_now_micros()`'s return typing, in `i64`
  subtraction, or in string interpolation of the result. The three-way split
  should be resolved by printing each of `a0`, `a1`, and `a1 - a0` separately.
