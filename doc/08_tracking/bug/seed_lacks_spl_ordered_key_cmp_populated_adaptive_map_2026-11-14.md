# Seed interpreter cannot run a populated AdaptiveMap (spl_ordered_key_cmp unbacked)

Status: verification-pending (tagged workaround, not a fix)

`AdaptiveMap`/`AdaptiveSet` call `spl_ordered_key_cmp` / `spl_collection_capture_*` once they hold entries. The seed
(`seed-tip`) reports `unknown extern function: spl_ordered_key_cmp`, so
`test/01_unit/compiler/35.semantics/collection_static_select_populated_spec.spl` (lookup results equal under linear/hash/ordered
after SDN selection) fails there. Same limit is documented in `test/01_unit/lib/collections/adaptive_policy_adapter_spec.spl`.

Workaround: that case lives in its own spec tagged `@tag:in-development` naming this blocker; the empty-container flip specs run green.
Fix: back the externs in the seed or run the populated spec on a runtime that links them.
