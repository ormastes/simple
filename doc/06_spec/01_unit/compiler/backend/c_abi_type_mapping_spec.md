# Shared C ABI type mapping scenarios

Authored manual; executable qualification UNRUN.

The existing actual mapper scenarios preserve primitive/bool, named struct/enum and opaque/integer-width behavior. The added case checks explicit I16/U16/U32 spellings and canonical scalar validity for NUL, supplementary/highest scalars and surrogate rejection. These controls do not qualify an implicit primitive Char ABI.

Three negative API fixtures call the shared mapper and actual C/C++ header emitters with direct Char. Each must fail specifically with E-CHAR-FOREIGN-ABI before the missing-refusal sentinel; generic process failure is not a pass. They are authored UNRUN and use the existing admitted fixture workflow only. Recursive foreign metadata, primitive physical storage, actual C calls and runtime/performance remain outside this narrow prerequisite.
