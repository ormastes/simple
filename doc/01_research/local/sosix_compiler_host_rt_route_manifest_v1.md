# SOSIX compiler-host `rt_*` route census, V1

**Source commit:** `3eb562867e7` (`origin/main` at collection).  **Machine-readable
inventory:** [sosix_compiler_host_rt_route_manifest_v1.json](sosix_compiler_host_rt_route_manifest_v1.json).

This is the compiler driver and loader portion of RU-001 in the [SOSIX
unification design](../runtime/sosix_unification/simple_sosix_runtime_unification_design_plan_2026-09-05.md).
It supports platform-unification REQ-002, REQ-009, and REQ-010. It is a
versioned research snapshot, not the production operation registry or a claim
that the ordinary compiler runs inside SimpleOS.

## Scope and method

The inventory covers direct `extern fn rt_*` declarations in
`src/compiler/80.driver/**` and `src/compiler/99.loader/**`. For each symbol it
records the declared signature variants, declaration sites, lexical call sites,
interpreter binding where `interpreter_extern/mod.rs` registers one, current
route, proposed destination, consumer profile, and migration disposition.
Native provider ownership and SimpleOS availability remain explicitly
unresolved. Lexical call sites require review: strings and inline comments can
match. The category assignments are provisional until the owning contract is
reviewed.

| Observation | Count |
|---|---:|
| Direct declarations | 216 |
| Distinct symbols | 90 |
| Symbols with an interpreter registration | 78 |
| Symbols without an interpreter registration | 12 |
| Symbols with conflicting declared result types | 3 |

The three declaration conflicts are `rt_env_get` (`text` versus `text?`),
`rt_file_read_text` (`text` versus `text?`), and `rt_process_run` (tuple versus
`ProcessRunResult`). These are declaration-contract conflicts; this census does
not assert that every variant reaches execution. Draft PR #1819 removes the
compiler cache's struct-shaped `rt_process_run` declaration, but it is not part
of the pinned main commit.

The missing interpreter registrations are `rt_file_write`, five
pinned-archive calls, `rt_process_start_identity`, two Simple ABI version
calls, `rt_time_millis`, `rt_time_now_iso`, and `rt_uuid_v4`. Absence from the
registry is a routing gap to classify, not proof that each operation should be
interpreter-callable.

## Migration consequences

1. Resolve the true native owner and execution profile for every OS-service
   row. A Rust interpreter handler is not native-provider or SimpleOS evidence.
2. Reconcile the three signature conflicts against the canonical runtime ABI
   before replacing direct declarations with shared facades.
3. Migrate compiler file, environment, process, path, time, and mapping effects
   behind SOSIX contracts and providers. Preserve language/runtime intrinsic
   rows outside the OS-service namespace. Qualify interpreter, native, and
   SimpleOS behavior with the same observable contract.
4. Extend RU-001 to the remaining service declarations, POSIX imports, Future
   implementations, rendering, and provider ownership. This bounded inventory
   does not close the full P0 gate.
