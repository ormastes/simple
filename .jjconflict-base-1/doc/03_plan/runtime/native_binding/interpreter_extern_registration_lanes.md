# Interpreter Extern Family Registration Lanes

Status: plan (dispatch document). Precedent: the `rt_sdl2_*` registration
(66 entry points) at
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2567` +
`interpreter_extern/sdl2.rs` (typed transmute table at `sdl2.rs:262-350`),
sabotage-verified. Companion plan: `dlopen_conversion_lanes.md` (same dir) —
ground rules §1–§7 there apply verbatim to every lane here; not repeated.

**Exclusion:** `rt_vulkan_*` has a lane in flight elsewhere — NO lane here may
touch it. (`rt_vk_*` is a different prefix; see M3.)

## Why one mechanism cannot serve everything (decided on paper)

The existing `dynamic_sffi::try_call_dynamic` fallback (`mod.rs:2615`) returns
**everything as `i64`**. Any family with `const char*`, `double`, or `bool`
returns needs a typed table (the `sdl2.rs` shape). Measured family shapes
(distinct symbol counts, `/usr/bin/grep -ohE 'rt_<fam>_[a-z0-9_]+'` over
`src/runtime/*.{c,h}` vs `src/{lib,app}` `.spl` callers, 2026-08-05):

| family | C defs | .spl uses | mechanism |
|---|---|---|---|
| `rt_glfw_*` | 51 | 39 | M1 — C impl linked (`runtime_glfw.c` in default source list) |
| `rt_sdl3_*` | 33 | 22 | M1 — C impl linked (`runtime_sdl3.c` in default source list) |
| `rt_opengl_*` | 18 | 19 | M2 — C defs exist but source-list membership UNVERIFIED |
| `rt_oneapi_*` | 14 | 25 | M2 — same |
| `rt_webgpu_*` | 3 | 16 | M3 — capability gap, not a registration gap |
| `rt_vk_*` | 1 | 25 | M3 |
| `rt_gui_*` | 1 | 17 | M3 |
| `rt_lyon_*` | 0 | 49 | M3 |
| `rt_gamepad_*` | 0 | 20 | M3 |

- **M1** (registration gap): copy `sdl2.rs` — a prefix arm in `mod.rs`
  dispatching to a per-family module that resolves the symbol in the linked
  runtime and calls through a typed table. Signatures enumerated from
  `src/runtime/runtime.h` + the defining `.c`; every non-`i64` return gets a
  typed row; unknown signature = explicit error, never a guessed transmute.
- **M2** (possible SDL2 root-cause shape): FIRST check whether the defining
  `.c` file is in the default source list at
  `src/compiler/70.backend/backend/runtime_compiler.spl:268` and in the seed
  build; if absent, that is the real bug (SDL2's was) — fix list membership,
  THEN register as M1.
- **M3** (capability gap): the family has (almost) no native definition
  anywhere. Registering a dispatcher cannot conjure an implementation.
  Decided: register a prefix arm returning a **structured capability error**
  (`"<family>: no native implementation (capability gap, tracked in
  native_library_binding_survey.md §1)"`) so callers can distinguish
  "unregistered" from "unimplemented". Real backends are Task #62 territory
  (see companion doc, "not worth a lane now"). This is deliberately cheap.

## Lane graph

```
Now:  R1 (glfw+sdl3, M1)   R2 (opengl+oneapi, M2)   R3 (M3 honest arms)   R4 (509-name census)
```
All four are mutually independent (disjoint files). R1/R2/R3 all edit
`mod.rs` — **R1 owns the `mod.rs` edit**; R2 and R3 deliver their prefix-arm
hunks as patches in their reports if R1 has not landed, or land after R1
(serialize `mod.rs` commits: R1 → R2 → R3; all other files are disjoint so the
work itself is concurrent).

---

## R1 — `rt_glfw_*` + `rt_sdl3_*` registration (M1)

**Owns:** `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` (ONLY new
prefix arms next to the `rt_sdl2_` arm at `:2567`),
`src/compiler_rust/compiler/src/interpreter_extern/glfw.rs` (new),
`src/compiler_rust/compiler/src/interpreter_extern/sdl3.rs` (new),
`test/01_unit/compiler/interpreter_extern/glfw_registration_spec.spl` (new),
`test/01_unit/compiler/interpreter_extern/sdl3_registration_spec.spl` (new).

**Task:** clone the `sdl2.rs` shape per family. Enumerate the 51/33 symbol
signatures from `runtime.h` / `runtime_glfw.c` / `runtime_sdl3.c`; typed rows
for every non-`(i64...) -> i64` shape. Include the same
family-matches-C-source guard the SDL2 lane added, so the arm refuses names
with no C definition instead of transmuting garbage. Host truth: `libglfw.so.3`
and `libSDL3.so.0` are both ABSENT on this host and both C impls already
dlopen — so the observable result is an honest per-library unavailability,
which is exactly what the specs assert.

**Gate (engine: seed interpreter — this registration lives in the seed; JIT
and native are NOT covered and the report must say so):**
```
SIMPLE_EXECUTION_MODE=interpret bin/simple test \
  test/01_unit/compiler/interpreter_extern/glfw_registration_spec.spl \
  test/01_unit/compiler/interpreter_extern/sdl3_registration_spec.spl \
  --no-cache --no-cover-check > /tmp/r1.log 2>&1; /usr/bin/grep -a "SPEC FILE VERDICT" /tmp/r1.log
```
Receipt: two verdict lines, each `failed=0 dropped=0`, combined `executed>=8`.
Required assertions: (a) calling e.g. `rt_glfw_init` no longer yields
`unknown extern function: rt_glfw_init` — assert the error text CHANGED to the
family-level result (this is the resolution oracle; exit status is fail-open);
(b) a name in the prefix but with no C definition (e.g. `rt_glfw_zzz_bogus`)
returns the guard's refusal, not a crash; (c) same for sdl3. NOTE: the seed
must be rebuilt for the new arms to exist — prove the rebuilt binary
positively via (a) going green, never via banner/mtime; budget the rebuild.
**Sabotage:** comment out the `rt_glfw_` prefix arm, rebuild, re-run →
assertion (a) RED with the original unknown-extern text. Revert, re-confirm.
**Size:** 2 agent-sessions (signature enumeration is the bulk; 84 symbols).
**Status: dispatchable now.**

## R2 — `rt_opengl_*` + `rt_oneapi_*` (M2: source-list first)

**Owns:** the defining `.c` files (locate:
`/usr/bin/grep -rln "rt_opengl_\|rt_oneapi_" src/runtime --include='*.c'`),
`src/compiler/70.backend/backend/runtime_compiler.spl` source/object list
lines ONLY IF the check shows absence — coordinate with lane N2 of the
companion doc, which owns the same lines for `runtime_renderdoc`; serialize
those two commits),
`src/compiler_rust/compiler/src/interpreter_extern/opengl.rs`, `oneapi.rs`
(new), their `mod.rs` prefix arms (after R1 lands),
`test/01_unit/compiler/interpreter_extern/opengl_registration_spec.spl`,
`.../oneapi_registration_spec.spl` (new).

**Task:** Step 1 — determine whether each defining `.c` is in the default
runtime source list AND the seed build; record the answer in the report either
way (this is the SDL2 root-cause check the campaign generalizes). Step 2 — fix
membership if absent. Step 3 — register as M1 with typed tables (18+14 syms).
**Gate:** same shape as R1, per-family specs, combined `executed>=6`,
error-text-change oracle, bogus-name guard assertion. Engine: seed
interpreter only. **Sabotage:** same shape as R1 (drop the arm → RED).
**Size:** 1–2 agent-sessions. **Status: dispatchable now** (its `mod.rs` hunk
lands after R1).

## R3 — M3 honest capability arms (`rt_webgpu_ rt_vk_ rt_gui_ rt_lyon_ rt_gamepad_`)

**Owns:** `src/compiler_rust/compiler/src/interpreter_extern/capability_gap.rs`
(new — ONE module, a prefix→message table for all five families), its `mod.rs`
arm (after R1/R2 land),
`test/01_unit/compiler/interpreter_extern/capability_gap_spec.spl` (new).

**Task:** each of the five prefixes returns the structured capability error
(wording above), NOT a plausible value and NOT `unknown extern function`.
Do NOT touch `rt_vulkan_` (in-flight lane; `rt_vk_` only). `rt_lyon_` (49
uses) and `rt_gamepad_` (20 uses) have real callers — the report must list the
top callers so a future backend lane has a reachability starting point.
**Gate:** `executed>=10` (two assertions per family: error text is the
capability message; text differs from the pre-lane unknown-extern text).
Engine: seed interpreter. **Sabotage:** make `rt_lyon_` return a fake success
value 1 → RED.
**Size:** 1 agent-session. **Status: dispatchable now** (`mod.rs` hunk queues
behind R1/R2).

## R4 — the ~509 unreachable names (census, not implementation)

**Owns:** `doc/08_tracking/bug/interpreter_extern_unreachable_names.md` (new,
tracking doc only — no product code).

**Task:** regenerate the "reachable from neither the static table nor the
runtime `.so` exports" set (the ~509) with the census method of
`doc/08_tracking/bug/undeclared_imported_symbols_census.md` (whose measured FP
discipline applies — hand-verify a deterministic sample and report the FP
rate). Bucket each name: (a) served by R1–R3 once landed, (b) M3 capability
gap, (c) dead caller (delete-candidate), (d) genuinely missing registration →
file follow-up. **Gate:** the doc contains the full enumeration + per-bucket
counts + a stated FP-rate from a ≥20-name hand-verified sample; spot-check
command included for each bucket. **Sabotage (census-grade):** seed the
scanner input with one known-registered name (`rt_sdl2_init`) — it must NOT
appear in the output set; if it does the method is broken.
**Size:** 1 agent-session. **Status: dispatchable now.**
