# module_static_unresolved_initializer

Status: workaround applied, root fix open. Found in Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: cannot derive module static type from unresolved initializer (compiler.frontend.core.parser, par_lexical_bindings).

Workaround (tagged `@workaround bug=module_static_unresolved_initializer_2026-10-24`): explicit annotation (src/compiler/10.frontend/core/parser.spl).

Root fix location: src/compiler/50.mir/_MirLowering/module_lowering.spl: derive static type from a struct-literal constructor of an imported struct.
