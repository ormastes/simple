# Target-bound compiler cache identity

Requirement: REQ-GENERIC-CONFIG-TARGET-001, generic hardening plan §6/P4.
Status: authored manual and eight executable SSpec scenarios; runtime and docgen UNRUN.

The tests call the actual driver options adapter, production hash owner, 16-byte serialization and cache validator. They require a target-only change to return CACHE_STALE under the default moderate policy and unbounded-budget sentinel. Identical requests remain CACHE_FRESH. Other cases preserve omitted defaults and verify independent target, backend, policy, budget and framed-text discrimination.

Executable owner: `test/01_unit/compiler/cache/compile_options_target_identity_spec.spl`.
Run through the existing qualified pure-Simple SSpec runner, then existing spipe-docgen; no substitute harness or scanner establishes this acceptance. Native/interpreter/cold-warm and broader core/lib/MCP gates remain unrun. This fixture validates the actual hash/driver/codec boundary, not a full linker or dynload publication run.
