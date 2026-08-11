# Capability Interfaces Skill — writing/extending a capability library

Use when adding, extending, or debugging a **capability** trait pair/group —
debug/profile is the worked example (`src/lib/common/debug/`).

Full guide: `doc/07_guide/language/capability_library_authoring.md`
Feature hub: `doc/00_llm_process/feature_expert/debug_profile/skill.md`

## 0. The one hazard — read before writing a line

Classes are **value types** (`val b = a` copies) and **nothing warns**. Assume
any handle you hold is a copy until proven otherwise.

1. **Pairing diverges copies.** A group built from two accessors
   (`session.debug()` + `session.profile()`) holds two diverging copies. Measured
   8/70 RED, `expected 6, got 0`.
2. **`fn` discards mutation.** A `fn` trait method receives a copy. Every
   mutating method must be `me`. (Doesn't bite for class-typed fields, but `me`
   is still the default.)
3. **Acquisition position decides aliasing.** A handle stops aliasing unless it
   is a function's **tail expression**. Symptom: `step`/`resume` work,
   `set_breakpoint`/`profile_begin` silently do nothing — reads as "backend
   can't profile".

**Safe shapes:** class-typed session field held directly · `launch()` with no
bound handle · acquisition returned as the tail expression.

## 1. Shape the traits

- **Core trait** — the minimum every backend answers. **Accessors live here**
  (`kind()`, `debug_level()`, `profile_level()` — plain `fn`, they don't mutate).
- **Enhanced trait** — optional capability. Don't put an optional method on the
  core trait with a sentinel return; that's what `CapLevel` is for.
- **Group** — one trait over one value, union of members, zero new methods,
  **one** accessor. Name it `<backend>_debug_profiler(session)` so the
  `dynamic_capability_acquire` lint recognises it.

Write the group **longhand**. The `trait G with A, B:` sugar parses but is
**INERT**: `desugar_traits` has no compile-path caller (only the standalone
`app.desugar` tool), and the deployed seed predates the parser change.

## 2. Be honest in `CapLevel` / reports

- `Native` = real device mechanism · `Emulated` = software model ·
  `Unavailable` = nothing measured. `cap_level_name` is **lowercase**.
- `PROFILE_ABSENT = -1` is the ONLY honest "not measured". Reporting `0` is a
  contract violation. Use `profile_report_unavailable(detail)`.
- Arm profiling **at attach** (`AttachOpts.profile`) — GPU PROF-1 can't be
  enabled after upload.
- Contract details specs assert: `set_breakpoint` returns **false** if already
  present; `breakpoints()` **ascending**; `read_mem` returns **empty** on
  overrun.

## 3. Critical mode

Config `config/critical_mode.sdn`; acquire once under `@init_phase` (DCA001);
GPU backend must be pinned, `auto` is DCA002; on pin/probe mismatch print the
`REFUSING TO START` report and stop — never continue on the probed backend.

Note: `if val` is AOT-broken (real `nil` → `SOME` under `native-build`), so a
generated capability check would fail **OPEN** natively. Don't add one yet.

## 4. Test it so the test can fail

- **Assert on execution, not text/structure.** A generator spec passed 21/21
  while emitting code that could not compile.
- **No disjunctive specs.** "skips cleanly OR matches ref_vm" is unfalsifiable.
  Emit the branch (`DEVICE-RAN:` / `SKIPPED: … the DEVICE-RAN branch did NOT
  run`) and support `SIMPLE_REQUIRE_GPU=1`. `step()` text is **swallowed** on
  passing runs — use `print` or assert messages.
- **Sabotage the oracle.** A real launch-count floor sabotages to
  `expected 20 to be greater than 100000`. Remove your guards and confirm the
  spec goes RED.
- **No gate tautologies.** Asserting only `test_env_require(...) ==
  "blocked:..."` is green *because* the gate is shut. **The fix is NOT flipping
  the expectation to `ready`** — assert on behaviour behind the gate, and don't
  claim `@cover` for what you can't reach.
- **Green ≠ reachable.** Grep for callers. `desugar_traits`, `svmg_lowering`,
  and `action_key`/`interface_digest` are all landed, specced, and callerless.

## 5. Honesty when reporting

All evidence to date is from the **Rust seed** — none is self-hosted. CUDA and
Vulkan genuinely run on device (20 launches each). **Metal's device path is
unverified** (`svmg_metal_kernel.metal` has never been compiled by any Metal
compiler) — never imply Metal works. DAP GPU attach is **routing-only**: there
is no `.spl` → SVM-G path.
