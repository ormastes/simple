# Is Simple's current grammar sufficient for an Amaranth-style RTL-generation eDSL emitting VHDL?

**Date:** 2026-07-26 · **Status:** Research (no code changes)

## TLDR (verdict: YES, sufficient — with one hard constraint and known landmines)

- **Verdict: the current grammar IS sufficient** for a Python/Amaranth-style
  elaboration-time RTL eDSL that emits VHDL. Elaboration is ordinary Simple code;
  widths are ordinary `i64` values. Precedent already in-tree:
  `src/lib/hardware/fpga_linux/soc_vhdl_gen.spl` (+ `_SocVhdlGen/`) is exactly this
  pattern (string-template VHDL generator, GHDL/Vivado-proven), and
  `src/compiler/70.backend/backend/vhdl*` is a full Simple→VHDL compiler backend.
- **Hard constraint: NO user-type operator overloading.** No trait `Add`, no dunder
  methods, no `operator` syntax anywhere in `25.traits`, stdlib, or guides.
  `+`, `@` etc. are built-in-type only. → **The eDSL must use method chaining**
  (`a.add(b)`, `a.eq(b)`, `sig.bit(3)`), Amaranth-value-methods-style.
- **(a) Width-parameterized 32/64 templates: YES today** via the runtime-config-struct
  pattern (`XlenConfig` in `src/lib/hardware/riscv_common/xlen.spl`). No const
  generics exist (generics are `<>` type params, monomorphized in `40.mono`), but
  const generics are NOT needed: width is just a field consumed at elaboration time.
  This would actually IMPROVE on today's duplicated `generate_*_vhdl` /
  `generate_*_vhdl_rv64` function pairs.
- **(b) AOP JTAG weaving: language AOP exists** (`on pc{ execution(* f(..)) } use advice
  before priority N`, woven by `driver_pipeline.weave_aop` → `50.mir/mir_aop_injection.spl`,
  fail-closed W2-B accounting into VHDL codegen). BUT it weaves *Simple functions*,
  not netlist structure, and the deployed seed interpreter weaves entry-module-only
  (Gap 1, OPEN — `doc/08_tracking/bug/aop_hart_hooks_weaving_gaps_2026-07-22.md`).
  → **Weave JTAG/DM hooks at the netlist-IR level inside the generator library**
  (a transform pass over the eDSL's module graph adding DMI ports/logic); optionally
  keep language-AOP as a second seam on elaboration functions once Gap 1 closes.
- **Top landmines for a generator workload:** seed `.push()` O(N²) clone (join
  pre-sized arrays or index-assign), Dict iteration order random per process
  (never iterate Dicts when emitting — sort keys or use arrays), interp struct
  name collisions across modules (prefix eDSL type names), cross-import
  module-global breakage in native build (use accessor fns for the signal-ID
  counter), nested closures can't mutate outer vars (use builder-object state,
  not closure capture, for `m.If(...)` blocks).

---

## 1. Grammar/feature inventory vs. eDSL needs

Sources: `doc/07_guide/quick_reference/syntax_quick_reference.md`,
`doc/07_guide/language/` (type_system, module_system, strictness_tiers),
`.claude/rules/language.md`, compiler layer layout `src/compiler/{25.traits,40.mono}`.

| eDSL need | Simple support | Notes |
|---|---|---|
| Operator overloading on user types (`Signal + Signal`) | **NO** | No trait-based dispatch (`trait Add` absent from `25.traits`/stdlib), no dunder/`operator` syntax in guides or parser. Built-in ops only; tensor `@`/pipeline `|>`/`>>` are compiler-special-cased for built-in types. |
| Generics | `<>` type generics, monomorphized (`src/compiler/40.mono/`) | Type params only. **No const generics / value parameters** (`Signal<32>` impossible). |
| Width parameterization | **Runtime config struct** — `XlenConfig` pattern (`xlen.spl`: xlen/mask/sign_bit/bytes_per_reg fields + `truncate`/`sign_extend_*` methods) | Sufficient: elaboration executes as normal code, width is a value. Already used across rv32/rv64 cores. |
| Traits/mixins/composition | Yes (no inheritance, by design) | Fine for `Elaboratable`-style protocol: `trait Elaboratable: fn elaborate(cfg) -> ModuleIr`. |
| Enums with payloads + `match` | Yes | Ideal for the netlist IR (`ExprIr.Add(a, b)`, `StmtIr.Assign(...)`, `PortDir.In/Out`). |
| String interpolation | `"{expr}"` — works incl. bootstrap MIR path (brace bug RESOLVED 2026-07-17, `bootstrap_mir_interpolation_literal_braces_2026-07-11.md`) | VHDL text contains no `{`/`}`, so interpolation is clean for VHDL. Caveat: **XDC/Tcl output DOES use braces** (`get_ports {x}`) — `xdc_gen.spl` already handles this; escape as `{{`/`}}` there. |
| Lambdas / blocks / chaining | `\x: x * 2`, placeholder `_ * 2`, method chaining | Chaining caveat: chains fail when a link's receiver type is erased (from ANY/Dict) — keep the IR fully typed, use intermediate typed `val` when needed. |
| Compile-time eval | None needed | Elaboration IS the "compile time" of the eDSL; it runs as ordinary interpreted/compiled Simple. |

## 2. AOP surface and applicability to RTL weaving

- Grammar (proven in `src/lib/hardware/debug_hooks/hart_debug.spl`):
  `on pc{ execution(* hart64_step_body(..)) } use hart_dbg_on_step before priority 10`.
- Pipeline: `80.driver/driver_pipeline.spl` `weave_aop` → `50.mir/mir_aop_injection.spl`,
  with W2-B fail-closed accounting: requested>0 ∧ woven=0 ⇒ CodegenError **in VHDL
  generation** (0c5210c8ff2) — the AOP and VHDL backends are already coupled.
- State (bug doc 2026-07-22): Gap 2 (MIR matcher rejected tokenized `execution ( ... )`
  predicates) **FIXED** with cross-matcher parity spec. Gap 1 **OPEN**: the deployed
  Rust-seed interpreter weaves only entry-module-defined functions, so aspects
  targeting imported lib modules never fire on `bin/simple run` until the
  self-hosted deploy lands.
- **Conclusion for the eDSL:** language-AOP intercepts *function execution at
  elaboration time* — it can wrap/extend generator functions, but it cannot express
  "add a DMI port and mux to every generated entity" structurally. JTAG debug-hook
  weaving (extra ports, DM bus, halt/step logic — cf. hand-written
  `src/lib/hardware/debug/{debug_registers,dmi_bus}.vhd`) is a **netlist-IR
  transform**: a library pass `weave_debug(module_ir, dm_cfg) -> ModuleIr` that walks
  the eDSL IR and injects ports/processes. That is deterministic, testable, works on
  today's deployed binary, and is exactly the AOP concept applied at the right IR
  level. Language-AOP remains useful as an *optional* seam (trace/counter advice on
  `elaborate()` calls) once Gap 1 closes.

## 3. Existing RTL-expression patterns in-tree (precedent)

- **Library string-generator (Amaranth's "emit" half):**
  `src/lib/hardware/fpga_linux/soc_vhdl_gen.spl` + `_SocVhdlGen/` — per-peripheral
  `generate_*_vhdl() -> text` functions, VHDL-2008, BRAM-inference aware,
  silicon-proven on KV260. Weakness the eDSL fixes: rv32/rv64 duplication
  (`generate_wb_interconnect_vhdl` vs `..._rv64`, separate product-bus wrappers)
  instead of one width-parameterized generator.
- **Behavioral models:** `src/lib/hardware/riscv_common/` (alu/decode/csr/memory) +
  `rv32i_rtl`/`rv64gc_rtl` cores parameterized by `XlenConfig` — proof that
  "runtime config struct instead of const generics" scales to a full CPU.
- **Compiler VHDL backend:** `src/compiler/70.backend/backend/vhdl_entity_compile.spl`,
  `_VhdlProcess/{process,terminator}_codegen.spl`, `vhdl_validation.spl`,
  `vhdl/vhdl_kernel_{entity,pipe}.spl` — compiles Simple functions themselves to
  VHDL entities. An eDSL is complementary (explicit structural netlists vs.
  compiled behavior); both can share `vhdl_validation`-style checks.

## 4. Landmines for a generator workload (impact + mitigation)

| Landmine | Impact on VHDL emitter | Mitigation |
|---|---|---|
| Seed `arr = arr.push(v)` clones whole array (O(N²)) | Emitting a 10k-line VHDL file line-by-line via push is quadratic in the seed interpreter | Pre-size array + `arr[i] = v` (fast path), or chunked `text` concatenation + single `join`; benchmark under the seed, not just native |
| Seed `Dict.keys()` order random per process (flat-lane nondeterminism root cause) | **Non-deterministic RTL output** → spurious diffs, broken caching, unreproducible synthesis | Never iterate Dicts during emission: keep ports/signals/statements in arrays in declaration order; if a Dict is unavoidable, sort keys before iterating; add a golden-file determinism spec (emit twice in two processes, byte-compare) |
| Interp global struct-name registry collision (same struct name in 2 modules) + fn-registry `use`-import hijack (2026-07-26) | eDSL names like `Signal`, `Module`, `Port` are collision-prone with other libs in interpreter mode | Use distinctive names (`RtlSignal`, `RtlModule`) or a unique prefix; keep the eDSL in one module tree |
| Cross-import module-level globals broken in native build | A global next-signal-ID counter breaks when imported | Wrap counter in accessor fns (proven workaround), or thread an `ElabContext` value through elaboration (better: also fixes determinism) |
| Nested closures can't MUTATE outer vars | Amaranth-style `with m.If(cond):` via closures that append to the module fails | Builder-object state: `m.if_(cond).then(\b: b.assign(...))` where the builder owns the statement list; or explicit `m.push_scope()/pop_scope()` |
| `it` blocks ignore `return` in interp | Early-return in specs silently continues | Structure emitter specs without early return |
| Chained methods on erased receivers fail | `dict[k].add(x).eq(y)` breaks | Intermediate typed `val`; keep IR arrays typed |
| Arrays are value types (pass-by-copy) | Passing a big statement-list array copies it | Hold lists inside a struct/builder passed once, or index into a central store |
| JIT `Option<i64>` payload 3 reads as None | An optional width/index of literal 3 vanishes under JIT | Avoid `Option<i64>` in IR; use sentinel −1 or a payload enum |
| `{`/`}` in generated text (XDC/Tcl only) | `{name}` would interpolate | `{{`/`}}` escapes; VHDL itself is brace-free (verified: interpolation bug is RESOLVED anyway) |
| ONE module-level `extern fn` breaks native-build ("MIR module has no functions") | eDSL must not declare externs | Pure Simple only — a VHDL emitter needs none |

## 5. Ranked conclusion

**Must-fix (blocking) grammar bugs: NONE** — everything needed works today.

**Rank 1 — design-around constraints (accept, don't wait):**
1. No user-type operator overloading → **method chaining API** (`a.add(b)`, `a.eq(b)`,
   `m.d_sync(sig.assign(expr))`). This is the recommendation: chaining is fully
   supported, reads acceptably (Amaranth users already write `.eq()`), and avoids
   betting the eDSL on a new language feature.
2. AOP Gap 1 (entry-module-only interp weaving) → do JTAG weaving as a
   **netlist-IR transform pass** in the generator library, not via language AOP.

**Rank 2 — nice-to-have language features (file as feature requests, not blockers):**
1. Operator overloading via traits (`trait Add { fn add(...) }` + `+` dispatch) —
   would make the eDSL read like Amaranth (`a + b`); largest ergonomic win.
2. Const generics (`Signal<W: i64>`) — cosmetic only; `XlenConfig`-style value
   config already covers 32/64 templates.
3. Close AOP Gap 1 (all-modules interp weaving) — enables optional language-level
   elaboration hooks.

**Rank 3 — engineering disciplines (bake into the eDSL from day one):**
deterministic emission (arrays not Dicts, determinism golden spec), pre-sized
string building, ElabContext instead of module globals, distinctive type names,
no `Option<i64>` in the IR.

**Bottom line:** build the eDSL now as a pure-Simple library (netlist IR enums +
builder chaining + `XlenConfig`-style width config + a debug-weave IR pass),
reusing `_SocVhdlGen` emission idioms and `vhdl_validation` checks; file the
operator-overloading trait feature as the one ergonomic follow-up.
