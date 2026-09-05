# Statement coverage conflated line numbers across files (defect D)

**Status:** FIXED (this commit). One residual, tracked below, remains OPEN.
**Severity:** high — every measured statement-coverage number in the repo was an
upper bound, and the error only ever ran in the flattering direction.

## Defect

`span_to_location` (`src/compiler_rust/compiler/src/interpreter/coverage_helpers.rs`)
returned the constant `"<source>"` as the file for every recorded line:

```rust
let file = "<source>".to_string();
```

`Coverage::record_line` keys `line_hits: BTreeMap<String, BTreeSet<usize>>` by
that file, so every file in a run collapsed into ONE bucket keyed by line number
alone. The dump reported `total_files: 1` for a multi-file run. The reporter in
`src/app/test_runner_new/test_runner_single.spl` then took only the line column
(`hits[parts[parts.len() - 2]] = true`) and credited a target line when the line
number was hit ANYWHERE and the enclosing function had been called.

Consequence: line N executing in file A marked line N of file B covered whenever
B's enclosing function had also been called — for example an untaken error branch
inside a well-tested function.

## Reproducer

`test/01_unit/app/test/coverage_line_key_spec.spl` with fixtures in
`test/fixtures/coverage/`. `covkey_exec_a.spl` executes recordable lines 3..11;
`covkey_dead_b.spl` has recordable lines 4..11 that NEVER execute (its guard is
always false) while its enclosing function IS called. Hand-computed honest
coverage for B is 2/10 = 20%.

Before the fix:

```
coverage: test/fixtures/coverage/covkey_exec_a.spl 100% (9/9 lines)
coverage: test/fixtures/coverage/covkey_dead_b.spl 100% (10/10 lines)   <-- 80 points of pure inflation
```

After:

```
coverage: test/fixtures/coverage/covkey_exec_a.spl 100% (9/9 lines)     <-- honest 100% unchanged
coverage: test/fixtures/coverage/covkey_dead_b.spl 20% (2/10 lines)
coverage: test/fixtures/coverage/covkey_calls_c.spl 50% (3/6 lines)     <-- negative control
coverage: test/fixtures/coverage/covkey_toplevel_d.spl 66% (2/3 lines)  <-- residual, see below
```

## Fix

1. **Seed** — `span_to_location` reads `CURRENT_EXEC_MODULE`, the thread-local
   already saved/restored around `execute_function_body` (the single choke point
   all function-execution paths funnel through, established by defect B's fix).
   `None` maps to the existing `"<entry>"` sentinel. No new AST field and no new
   thread-local were needed; the plumbing already existed and coverage simply
   was not reading it.
2. **Reporter** — hits are keyed on `(file, line)` via `_cov_hit_key`. The
   collector emits absolute paths while `@cover` targets are repo-relative, so
   `_cov_recorded_file_for_target` matches on a `/`-anchored path suffix.

The enclosing-function gate is unchanged: a genuinely uncalled body still reads
as uncovered (defect B's standing rule). `covkey_calls_c.spl` is the negative
control for exactly that — one called and one uncalled function, 50% not 100%.

## Measured damage

Same specs, same binary, fix B held constant; the only variable is the hit key.

| module | reported | honest | delta |
|---|---|---|---|
| `style_block_resolve.spl` | 99% (314/317) | 87% (276/317) | -12 |
| `style_block_parse.spl` | 96% (472/488) | 85% (417/488) | -11 |
| `selector_matcher.spl` | 98% (71/72) | 87% (63/72) | -11 |
| `simple_web_html_engine2d_presenter.spl` | 48% (158/327) | 35% (117/327) | -13 |
| `html_tree_builder.spl` | 85% (238/277) | 79% (220/277) | -6 |
| `html_tokenizer.spl` | 79% (305/386) | 74% (288/386) | -5 |
| `dom_identity_index.spl` | 63% (149/234) | 59% (140/234) | -4 |
| `simple_web_html_layout_renderer_paint_tiles_gpu.spl` | **100% (66/66)** | **96% (64/66)** | -4 |
| `dom.spl` | 87% (69/79) | 62% (49/79) | -25 |
| `simple_web_html_layout_renderer_foundation.spl` | 32% (461/1398) | 23% (335/1398) | -9 |
| `style_block.spl` | 63% (103/162) | 57% (93/162) | -6 |
| `widget_to_dom.spl` | 74% (204/273) | 70% (193/273) | -4 |
| `style_rule_index.spl` | 15% (90/576) | 14% (82/576) | -1 |

Every module moved DOWN or stayed flat; none rose. A module reporting a clean
100% was really 96%.

## OPEN residual — flattened module top-level statements

An imported module's top-level statements are flattened into the entry program
before execution, so `CURRENT_EXEC_MODULE` still reads `<entry>` for them and
they are filed under `<entry>` rather than their own module. They therefore
report uncovered even when they ran: `covkey_toplevel_d.spl` measures 66% (2/3)
where the honest answer is 3/3.

This UNDER-reports, so a number is a floor, never a flattering estimate. It is
bounded: module-level recordable statements number <=2 lines (<=0.9%) in each of
the eight browser-engine campaign modules. Fixing it requires the flatten path to
carry the owning module through to execution.

Do NOT "fix" it by accepting `<entry>` hits for a target file — that re-pools
every module's top level into one bucket and reintroduces the conflation above.

## Sibling defect, NOT fixed here

`record_condition_coverage` is called with a hardcoded `"<source>"` file and
line 0 throughout `src/compiler_rust/compiler/src/interpreter/expr/ops.rs`
(~12 call sites). Condition/MC-DC coverage therefore has the same
non-attribution problem this fix removed from statement coverage. Statement
coverage is what `simple test` reports, so that path was fixed first.

## Also repaired as a side effect

`node_exec.rs` feeds `extract_node_location`'s file into
`DebugState::should_stop`, so the debugger's breakpoint file matching consumed
the same `"<source>"` placeholder and was equally broken. It now receives real
paths.
