# LLVM static text globals still need startup boxing

The LLVM literal fix boxes executable MIR Opaque("str") values through
rt_string_new_literal(ptr, explicit_byte_length). It deliberately leaves
static initializers out of that path.

MirToLlvm.translate_module emits MirModule.statics as direct LLVM global
initializers in src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl
around the Module-level mutable globals block. Bootstrap statics are emitted
as direct global constants in emit_bootstrap_statics in the same file.
translate_const_value is type-erased and renders a Str as a GEP constant;
the ordinary static path may wrap that address in ptrtoint. LLVM constant
initializers cannot call rt_string_new_literal, and this backend currently
has no module-init/global-constructor owner that could initialize tagged text
before reads.

Therefore a module-level static text value remains a raw address in this
patch. Do not treat local/direct-call/return literal qualification as proof
that static text globals are fixed. Resolve this separately by adding an
owned startup-initialization path, or reject such initializers until one
exists.
