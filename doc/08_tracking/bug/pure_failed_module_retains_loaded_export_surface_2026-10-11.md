# Failed pure interpreter module retains loaded export surface

Status: OPEN_SOURCE_ESTABLISHED; runtime reproducer and repair UNRUN.

The actual pure owner is src/compiler/10.frontend/core/interpreter/module_loader_core.spl.
load_module returns success immediately for module_is_loaded at line494. The normal
load path extracts declaration exports, registers functions and marks the module
loaded at line561 before checking dependency success and evaluating initializers.
Dependency failure at line591 and initialization failure at line605 return failure
without removing that early loaded state. A subsequent cached selective load at
line658 registers imported names from that failed owner and returns success.

This is source-established control flow, not an executed test result. It cannot
support the claim that declared exports are successfully evaluated exports.
The private Rust source-authority diagnostic does not qualify this pure path.

A safe repair needs LOADING/READY/FAILED states and committed evaluated export
records. Owner-qualified function routes exist, but values/structs/enums still
need equivalent owner evidence. Cleanup must remove failed-owner routes without
deleting or overwriting another module's registries; unmarking alone or calling
the current unload helper does not establish rollback. Cycles and repeated loads
need explicit semantics. No shared repair applied.

Required actual-owner regressions: failed dependency followed by second load;
failed initializer followed by selective import; function/value/struct/enum
re-export failure; same-name sibling owner preserved; valid cached import;
generation reset; loading cycle; failed-owner cleanup and retry. Test real
interpreter registration and binding APIs, not a declaration-name oracle.

Private implementation lane: sol_capture_wait_review. Astra interface/source
review required before admission. Bug database reconciliation pending; this
Markdown evidence is not a fabricated database update. Phase3 remains NOT PASS.