# compiler Layer Expert

## Role

Maintain process knowledge for the `compiler` layer: owned source, architecture links, expected tests, and boundary rules. Use this skill when a task changes `src/compiler` or depends on its public behavior.

## Pipeline Links

- [research](../skill_command/skills/pipe/research/skill.md)
- [design](../skill_command/skills/pipe/design/skill.md)
- [impl](../skill_command/skills/pipe/impl/skill.md)
- [verify](../skill_command/skills/pipe/verify/skill.md)
- [release](../skill_command/skills/pipe/release/skill.md)

## Layer Links

- [Source](../../../src/compiler/)
- [Architecture index](../../04_architecture/README.md)
- [Architecture modules](../../04_architecture/architecture_modules.md)
- [Design docs](../../05_design/)
- [Specs](../../06_spec/)
- [Collection planner: adaptive collections + typed queries (RC1 plan)](../../03_plan/compiler/collection_planner/adaptive_collections_typed_query_rc1_plan_2026-09-18.md)
- [mold-MDSOC++ linker (RC1 plan)](../../03_plan/compiler/linker/mold_mdsocpp_linker_plan_2026-09-18.md)

## Update Rule

When project work changes this layer's public contract, source ownership, tests, architecture, or verification requirements, update this skill with current links and handoff notes.

Template: [layer_skill.md](../../template/layer_skill.md)

- 2026-09-08 enum-pattern aliases: `interpreter_patterns.rs` resolves a
  qualified pattern's imported `EnumType` alias before comparing the runtime
  enum identity. Preserve the positive explicit-alias case and the negative
  conflicting-glob control in the focused Rust regression.

- 2026-09-05 gpu_frontend_offload: default-off frontend offload switch (`structural_contracts/frontend_offload_switch.spl`, driver gate in `80.driver/driver_source_pipeline_parsing.spl`) — see `doc/00_llm_process/feature_expert/gpu_frontend_offload/skill.md`.

- 2026-09-19 linker route (lane F1): the linker that links the `simple` binary
  is the **Simple-side** one, not the Rust seed's. `bin/simple native-build`
  is Simple (`src/app/cli/native_build_main.spl` -> `native_build_worker.spl`
  -> `cli_native_build_with_environment_variant_policy_v1` ->
  `driver_aot_native_output.spl:2235 link_llvm_native` ->
  `llvm_native_link.spl` -> `llvm_native_link_orchestrator.spl:648
  link_to_native`), and that is what
  `scripts/bootstrap/bootstrap-from-scratch.sh:2959,3036` runs for stage2 and
  stage3. The seed's `native_project/linker.rs` links only the cargo-built
  Rust artifacts and rejects `SIMPLE_LINKER=internal` by name
  (`linker_alias`). Two traps in the internal ELF engine's library search,
  both found by diffing `readelf -dW` against `ld.lld` rather than by reading
  the code: glibc's `libm.so`/`libc.so` are GNU ld **scripts**, and their
  `AS_NEEDED` keyword is separated from its `(` by whitespace (leaked
  `libmvec.so.1`); and the implicit libc path differs textually from the
  script's `GROUP()` member for the same file (duplicate `DT_NEEDED`). The
  engine emits one `DT_NEEDED` per shared input, so both showed up as extra
  entries ld.lld does not write. Plan §13 carries the route, the comparison
  table and the ranked gap list.

- 2026-09-19 linker route CORRECTION (lane F1 round 2): the entry above was
  wrong for stage 2. `bootstrap-from-scratch.sh:2945` sets
  `SIMPLE_NATIVE_BUILD_RUST=1` for the `:2959` stage-2 link, so
  `driver/src/main.rs:168-178` routes it to the **Rust** native-build
  (`native_build.rs:662` -> `native_project/mod.rs:1216 link_objects` ->
  `linker.rs:1165` -> `:54`), which refuses `SIMPLE_LINKER=internal` by name.
  The Rust linker therefore links stage-2 OBJECTS, not just cargo artifacts,
  and an internal bootstrap dies at stage 2. Only stage 3 is Simple-side, and
  via `bootstrap_main.spl:385` -> `bootstrap_focused_native_build` ->
  `bootstrap_api_fixed` -> `driver_aot_native_output` -> `orchestrator:648` —
  **not** `native_build_main.spl`/`native_build_worker.spl`. Third trap, worse
  than the two above because comparing the DT_NEEDED *set* cannot see it:
  DT_NEEDED **order** decides which library wins, ld.lld emits `-l` libraries
  before libc, and a libc-first list silently loses every shadowing symbol.
