# Configured module-child selection receipts

Status: authored manual; SSpec execution and generated-manual qualification BLOCKED.
Executable: `test/01_unit/compiler/hir/module_child_selection_receipt_v1_spec.spl`.

The fixtures use the real parser, surface registry freeze, and HIR import binding
owners with explicitly supplied frozen inventory/policy inputs. They do not claim
end-to-end inventory authentication or filesystem manifest parsing.

| Scenario | Expected observation |
|---|---|
| Public and private child names share one target | Different selected ordinals/modifiers remain retained; target identity is equal |
| Configured namespace differs from physical/parser label | Receipt retains `configured`, not `physical.pkg` |
| Corrupted ordinal, policy, snapshot or generation | Validator returns an explicit unavailable/mismatch reason |
| Current target content differs | SHA-bound receipt is rejected |
| Actual import binding, same-ID rebind, module reset | Initial binding has provenance; rebind/reset cannot reuse it |
| Namespace alias and qualified declaration binding | Capture follows the complete namespace write; both retain the selected child |
| Private route followed by public no-op import | Existing binding retains its private route |
| Frontend policy changes in the same snapshot | Semantic policy mismatch rejects the receipt |
| Producer mutates policy after freeze | Retained policy and receipt remain independent and valid |
| Legacy flat import has no selected manifest parent | Import behavior remains unchanged; receipt is unavailable |

A selected receipt is provenance, not permission. Explicit `pri` remains
file-private, omitted visibility remains immediate-folder scoped, and `pub`
classification cannot bypass a closed ancestor. This fixture does not qualify
those complete requester access decisions.
