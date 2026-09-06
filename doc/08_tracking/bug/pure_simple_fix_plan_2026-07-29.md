# Pure-Simple Divergence-Bug Fix Plan (2026-07-29)

Synthesis of 9 read-only investigation reports mapping the divergence-bug family
(already fixed in the Rust seed) into the **pure-Simple compiler + C/Simple
runtime**. Goal: land the same fixes on the natively-compiled pure-Simple binary
without touching Rust, per the user's runtime-language direction (pure Simple
first, else C in `src/runtime`, never Rust).

## 0. Key architectural facts (agreed across reports)

- **No active JIT in pure-Simple.** The divergence axis is **HIR tree-walk
  interpreter (the oracle)** vs **native-AOT codegen** (`70.backend` + linked
  runtime). `tiered_jit` is a dormant Rust bridge, not on the run/test path
  (reports 5, 8).
- **Result types are resolved STATICALLY per-local in `50.mir`**, not by runtime
  tag bits like the seed's Cranelift. So the seed's exact "missing result-type
  entry -> ANY -> no boxing" mechanism is not reproduced verbatim; its structural
  analog is the `MirType.i64()` default + `box_runtime_value` passthrough
  (report 1).
- **Runtime ABI has three layers** (report 0): (1) Rust
  `libsimple_runtime.a` — bootstrap-only for the seed but STILL referenced in the
  native link (`llvm_native_link.spl:1684-1690`); (2) C `src/runtime/runtime.c`
  (legacy `SplValue`) + `src/runtime/runtime_native.c` (canonical `rt_` tagged
  word ABI); (3) pure-Simple `50.mir` lowering that decides which `rt_` helper
  each print/join reaches.
- **UNRESOLVED CONTRADICTION — which formatter the native link actually uses.**
  Report 6 says the native LLVM path emits only `rt_*` calls and composite
  formatting resolves to the **Rust** `value_to_display_string`
  (`io_print.rs:452`), so tuple/dict are already fixed by the seed and enum/object
  are still broken there. Reports 0 & 7 say the active `rt_to_string`
  (`runtime_native.c:2393`) is the **C** one, which has NO tuple/dict/enum case
  and falls to `<value:0x%llx>`. Both cannot be simultaneously the live symbol.
  **This must be resolved first (Batch 0 below) — it decides whether tuple/dict
  need any pure-Simple/C work at all, or only enum/object do.**

## 1. SHARED-vs-SEED-ONLY split of the 13 session fixes

"Shared" = already benefits pure-Simple through a shared runtime symbol; needs at
most a **runtime relink/redeploy**, no compiler-side change. "Seed-only" = still
needs a pure-Simple compiler-side or C-runtime fix.

| # | Session fix | Pure-Simple status | Shared or seed-only |
|---|-------------|--------------------|---------------------|
| 1 | `string.to_float/to_f64/parse_float` pointer-not-value | ABSENT (C `rt_string_to_float` already reads `s->data` via strtod) | **SHARED** — relink only; C already correct (reports 0,2,7) |
| 2 | `join` renders elements empty | ABSENT (C `rt_array_join_any` normalizes each elem; lowering routes here) | **SHARED** — relink only (report 0) |
| 3 | tuple prints `<tuple@ptr>` -> `(a, b)` | Contested: SHARED if Rust formatter is live (report 6); PRESENT if C `rt_to_string` is live (reports 0,7) | **SHARED or SEED-ONLY — pending Batch 0** |
| 4 | dict prints `<dict@ptr>` -> `{k: v}` | Same contradiction as #3 | **SHARED or SEED-ONLY — pending Batch 0** |
| 5 | enum prints `<enum@ptr>` -> `Variant(payload)` | PRESENT (Rust Enum arm still `<enum@ptr>`; C has no enum case) | **SEED-ONLY** — needs C/Simple formatter (reports 6,0) |
| 6 | object prints `<object@ptr>` | PRESENT (Rust Object arm still `<object@ptr>`) | **SEED-ONLY** — needs C/Simple formatter (report 6) |
| 7 | `dict.set/insert` returns bool/nil not receiver | ABSENT (index-assign `d[k]=v` discards return; mutation preserved by in-place write-back `is_mutating_method`) | **N/A (bug not reproduced)**; residual chaining gap only (reports 0,4,7) |
| 8 | method results not tag-boxed -> raw int print | PRESENT (return types not threaded through `lower_method_call`) | **SEED-ONLY** — pure-Simple `50.mir` fix (reports 1,7) |
| 9 | bool method prints `1/0` not `true/false` | PRESENT (worked around by hardcoded name allow-list) | **SEED-ONLY** — pure-Simple `50.mir` fix (reports 1,7) |
| 10 | missing dispatch arm `sum` -> method-not-found | ABSENT (no closed dispatch table; resolves to stdlib) | **N/A (bug not reproduced)** (reports 3,7) |
| 11 | missing dispatch arm `max/min/count/unique/flatten/zip/entries/drop/skip/take/copy/insert` | ABSENT (all resolve to stdlib via generic fall-through) | **N/A (bug not reproduced)** (reports 3,5,7) |
| 12 | `appended/prepended/sorted/reversed/sort_desc` unavailable | PRESENT (no stdlib method, no C fn — unresolved symbol) | **SEED-ONLY (stdlib gap)** — pure-Simple `src/lib/common` (report 3) |
| 13 | legacy `rt_string_join` skips non-string elements | LATENT (not on native `[text].join` path, but still declared/callable) | **SEED-ONLY (latent)** — optional C hardening (report 0) |

**Counts:** SHARED (relink-only) = 2 confirmed (#1, #2) + up to 2 more (#3, #4)
pending Batch 0. SEED-ONLY needing a pure-Simple/C fix = 5 confirmed (#5, #6, #8,
#9, #12) + #13 latent + #3/#4 if C path is live. Bugs NOT reproduced in
pure-Simple = 3 (#7, #10, #11).

## 2. Runtime-language plan (where each runtime-side fix SHOULD live)

Direction: pure Simple first; else C `src/runtime`; never Rust. Where the working
implementation lives only in Rust today, it is a **port**, not new design.

| Fix | Target language/file | Port from Rust? |
|-----|----------------------|-----------------|
| #1 to_float value | Already C `runtime_native.c:3047` (correct) + pure-Simple twin `core_string.spl:1317` | No — already C+Simple |
| #2 join elements | Already C `runtime_native.c:3142` `rt_array_join_any` | No — already C |
| #3/#4 tuple/dict formatter | If C path live: NEW recursive formatter in C `runtime_native.c` near `rt_to_string:2393` (or pure-Simple). If Rust path live: already fixed, relink | **Port** the Rust `value_to_display_string` Tuple/Dict arms (`io_print.rs:504-550`) to C/Simple |
| #5 enum formatter | NEW C `rt_enum_to_string` walking `rt_enum_discriminant`+`rt_enum_payload` -> `Variant(payload)` (or pure-Simple), mirroring interpreter enum display | **Port** — Rust arm `io_print.rs:553` is still broken, so port the *interpreter's* correct rendering |
| #6 object formatter | NEW C/Simple `<Type>{field: v}` formatter mirroring interpreter | **Port** from interpreter oracle |
| #13 legacy `rt_string_join` hardening | C `runtime_native.c:3101` — route each element through `rt_interp_cstr` (optional, latent) | No — C-local hardening |
| #12 array methods | pure-Simple stdlib `src/lib/common` | No — new pure-Simple |

**Recommendation:** implement the aggregate formatter **once in C**
(`src/runtime/runtime_native.c`) covering tuple+dict+enum+object recursively via
`rt_to_string`, so a single symbol serves the native link, and mirror the
interpreter's output exactly (the interpreter is the oracle). Avoid touching Rust.

## 3. Pure-Simple bug table

bug | present? | exact fix_site (file:line) | lang | mirrors-seed-fix

- method results not tag-boxed (raw-int print) | **PRESENT** | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:873` (thread method return type into dest `MirType`); `switch_operators_calls.spl:906` (`lower_bootstrap_print_call`) | simple | #8
- bool method prints 1/0 | **PRESENT** | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:40-45` (`print_arg_is_bool_method_call` incomplete allow-list) + :972-975; real fix = each bool arm assigns `MirType.bool()` then delete allow-list | simple | #9
- unresolved-return default to i64 (structural ANY analog) | **PRESENT (risk)** | `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1107` (`MirType.i64()` default) + `box_runtime_value` :550-551 `case _:` passthrough | simple | #8
- direct print of untyped scalar SIGSEGVs | **PRESENT** | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:953-967` (`case _: ()` -> char* passthrough into `rt_print`) | simple | #8 (worse failure mode) |
- tuple/dict print wrong | **PRESENT iff C runtime is the live formatter** | routing: `switch_operators_calls.spl:953-967` add Tuple/Dict arms; formatter: NEW in `src/runtime/runtime_native.c` near `rt_to_string:2393` | c + simple | #3,#4 |
- enum print `<enum@ptr>` | **PRESENT** | NEW `rt_enum_to_string` in `src/runtime/runtime_native.c`; routing in `switch_operators_calls.spl` | c | #5 |
- object print `<object@ptr>` | **PRESENT** | NEW `rt_object_to_string` in `src/runtime/runtime_native.c`; routing in `switch_operators_calls.spl` | c | #6 |
- backend-interpreter fallback formats Dict/Tuple/Enum as `<TypeName>` | **PRESENT (if that path exercised)** | `src/compiler/70.backend/backend/interpreter_calls.spl:458-459` (`value_to_string`) | simple | #3,#4,#5 |
- `appended/prepended/sorted/reversed/sort_desc` unresolved | **PRESENT (stdlib gap)** | `src/lib/common/` add pure-Simple array methods | simple | #12 |
- to_float pointer-vs-value | ABSENT | `runtime_native.c:3047` / `core_string.spl:1317` (already correct) | c | #1 |
- join elements empty | ABSENT | `runtime_native.c:3142` (already correct) | c | #2 |
- dict.set/insert wrong return | ABSENT | mutation preserved by write-back `switch_operators_calls.spl:3296`; residual: `.set`/`.insert` not in method allow-list `method_calls_literals.spl:1141` (support GAP, not wrong-value) | simple | #7 |
- missing dispatch arm -> method-not-found | ABSENT | generic fall-through `method_calls_literals.spl:2202` resolves to stdlib | simple | #10,#11 |

**Confirmed-PRESENT pure-Simple bug count: 6 distinct defects** — (1) method
result tag-boxing / raw-int print, (2) bool method 1/0, (3) enum print, (4) object
print, (5) tuple/dict print *conditional on Batch 0*, (6) stdlib array-method gap.
Plus the backend-interpreter fallback formatter as a secondary path.

## 4. Verification path

**Cheapest run-capable full-CLI pure-Simple binary** (NOT the 3-stage `build
bootstrap`, whose stage4 peaks ~65 GB). Focused native-build of the CLI capsule
(report 7):

```bash
# Build a full-CLI pure-Simple native binary (single process, minutes)
SIMPLE_BOOTSTRAP_STAGE4=1 \
  bin/simple native-build \
    --entry src/app/cli/main.spl \
    -o build/fullcli/simple \
    --backend llvm \
    --runtime-path <libsimple_runtime.a-or-C-bundle>
# entry is allow-listed at bootstrap_focused_native_build.spl:70;
# the exact-capsule variant requires SIMPLE_BOOTSTRAP_STAGE4=1.
```

Note: the deployed `bin/release/x86_64-unknown-linux-gnu/simple` is a guarded
wrapper (prints "Build and use the pure-Simple bin/simple instead"); build the
capsule above rather than relying on it. Pre-built candidates under `build/`
(e.g. `build/aggfix/.../simple`, `build/redeploy_runtime/simple`,
`build/native_probe/simple`) exist but each needs a `--help`/`run` smoke to
confirm run-capability before trusting it.

**Run the divergence probes (oracle = HIR interpreter):**

```bash
# Oracle output (reference):    bin/simple run probe.spl
# Native output (under test):   build/fullcli/simple run probe.spl
# Divergence == any line where native != interpreter.
```

Probe set (one `fn main()` each; top-level never lowers the same way):
`("a",1)` tuple print; `{ "k": 1 }` dict print; an enum value print;
`[1,2,3].join(",")`; `"3.14".parse_f64()`; a `bool`-returning method printed
directly (e.g. `xs.contains(x)` and a user bool method); `[3,1,2].sorted()` /
`.reversed()` / `.appended(4)`. Compare each native line to the interpreter line.

## 5. Batched fix plan (file-disjoint = max safe parallelism)

**Shared-file bottleneck (pure-Simple backend):**
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` and
`method_calls_literals.spl` are touched by BOTH the tag-boxing/bool fixes AND the
aggregate-print routing. These edits **cannot be parallelized against each other**
— one agent owns each file, or serialize. `expr_dispatch.spl` is a third 50.mir
file that pairs with them.

- **Batch 0 (BLOCKING, do first — single agent):** Resolve the report-6 vs
  report-0/7 contradiction. Determine which `rt_to_string`/formatter symbol the
  native link actually resolves (inspect `llvm_native_link.spl:1684-1690` link
  order + `nm` the produced binary for `rt_to_string` / `value_to_display_string`
  provenance). Output decides whether #3/#4 are relink-only or need C work. No
  source edit — investigation only.

- **Batch A — pure-Simple 50.mir type-threading (single agent; shared-file
  bottleneck):** Fixes #8 + #9. Thread method return type through
  `lower_method_call` (`method_calls_literals.spl:873`); make each bool-returning
  method arm assign `MirType.bool()`; delete the `print_arg_is_bool_method_call`
  allow-list (`switch_operators_calls.spl:40-45`); harden
  `resolved_call_return_type` i64 default (`expr_dispatch.spl:1107`). Owns
  `method_calls_literals.spl`, `switch_operators_calls.spl`, `expr_dispatch.spl`.

- **Batch B — C runtime aggregate formatter (parallel with A; disjoint file):**
  Fixes #5, #6, and #3/#4 if Batch 0 says C path is live. Add recursive
  tuple/dict/enum/object cases to `rt_to_string` (`runtime_native.c:2393`) or new
  `rt_{tuple,dict,enum,object}_to_string`, mirroring the interpreter oracle. Owns
  `src/runtime/runtime_native.c` only. **Coupling:** the print *routing* for these
  lives in `switch_operators_calls.spl` (Batch A's file) — so the routing hunk
  must be sequenced after A, OR A and B coordinate on that one file. Cleanest:
  Batch A adds the routing arms (it already owns the file) and Batch B provides
  the symbols; they meet at the ABI, not the file.

- **Batch C — pure-Simple stdlib array methods (fully parallel; disjoint):**
  Fix #12. Add `appended/prepended/sorted/reversed/sort_desc` in
  `src/lib/common/`. No overlap with A or B.

- **Batch D — backend-interpreter fallback formatter (parallel; disjoint):**
  Add tuple/dict/enum arms to `interpreter_calls.spl:458-459` (only if that
  backend-interpreter path is exercised). Disjoint from A/B/C.

- **Optional Batch E — legacy `rt_string_join` hardening (#13):** route elements
  through `rt_interp_cstr` at `runtime_native.c:3101`. Same file as Batch B — fold
  into B, do not run concurrently.

**Recommended first batch:** Batch 0 (blocking investigation), then launch
**Batch A + Batch C + Batch D in parallel** (three disjoint files), with Batch B
starting as soon as Batch 0 resolves the formatter path and coordinating the
routing hunk with Batch A.

## 6. Not-a-bug notes (do not "fix")

- #7 dict.set/insert return, #10/#11 missing dispatch arms: NOT reproduced in
  pure-Simple. Only latent gaps (no `.set`/`.insert` method arm; a chaining caller
  consuming a `.set` return would get the int8_t flag). Add a `.set`/`.insert`
  method arm ONLY if that pattern must work — mirror the remove/delete arm at
  `method_calls_literals.spl:1296` (emit `rt_dict_set`, then `return
  receiver_local`).
