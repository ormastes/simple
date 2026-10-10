# Legacy direct declaration mirrors survive reset

Status: source repair and regression specs committed; UNEXECUTED.

The observed native probe (producer source 5e94f455, SHA 0e5695a3fb071b621eb3a2088fe9df08ce7e06f1f568da6288f2f2136fe62079) produced 97 HIR errors, including provider paths paired with preceding consumer import names. Evidence: /mnt/c/Temp/simple-pattern-payload-presence-native-20261010/cause-review.json. This symptom is not yet proven repaired.

The declaration owner writes SIMPLE_BOOTSTRAP_DECL_IMPORTS_<index> and reads it before restored arena imports in legacy mode. Reset removed SIMPLE_BOOTSTRAP_DECL_<index>_IMPORTS, a different key. Direct BODY, FIELD_NAMES and FIELD_TYPES writers/readers had the same reset omission. The repair removes these four direct keys within the existing declaration high-water loop; arena mode behavior is unchanged.

Bootstrap defaults to legacy declaration mode unless SIMPLE_NATIVE_ARENA_DECLS overrides it. The probe recorded SIMPLE_BOOTSTRAP=1, but inherited selectors were not fully captured and remain unknown. Tests explicitly select legacy mode, restore its prior environment value, assert real writer keys were present and then removed, and restore a real flat-pool import snapshot after another declaration occupied the same slot. No runtime PASS, full compiler qualification, or payload-transport fix is claimed.
