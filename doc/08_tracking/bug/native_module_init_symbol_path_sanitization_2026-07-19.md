# Native module-init symbols retain source-path punctuation

- **ID:** native_module_init_symbol_path_sanitization_2026-07-19
- **Status:** FIXED (LLVM smoke PASS; Cranelift initializer blocker tracked separately)
- **Severity:** high (valid native builds fail at generated C compilation)
- **Lane:** pure-Simple bootstrap plus Rust seed native-project linking

## Symptom

A cache-preserving current-source compiler build reached 1,362 objects, then
generated `_init_all.cpp` declarations such as
`__module_init_tmp__simple-native-bottom__...`. The `-` tokens made those C++
identifiers invalid on the shared Unix and Windows generator path.

## Root cause and fix

The four pure-Simple path normalizers now share the same portable rule: retain
ASCII letters, digits, `_`, `.`, and path separators; map every other Unicode
scalar to `_`; and strip absolute prefixes through `src/` or `examples/`.

The Rust bootstrap seed's `module_prefix_from_path` was the owner of emitted
object symbols and cache identity, yet preserved arbitrary path punctuation
when the configured root did not contain a discovered file. It now applies the
same prefix stripping and portable-character rule before either backend emits a
symbol. This deliberately renames every mangled symbol—not only module-init
symbols—for unmatched roots and punctuated components; prebuilt objects from
that unsupported naming scheme are incompatible, while cache keys miss safely.
Both lanes reject two distinct files that
sanitize to one module name before import merging, cache lookup, parsing, or
code generation.
The generated init caller is intentionally unchanged because renaming only the
caller would break linkage to the defining object.

## Regression

The existing hosted native smoke matrix now builds and reads a function-initialized
module global
from its already-hyphenated work directory under default LLVM and explicit
Cranelift on Linux, macOS, and Windows; FreeBSD exercises LLVM. LLVM passes the
focused hosted case. Cranelift reaches the separate module-global initializer
arity bug and remains an exact-diagnostic XFAIL; unexpected failures stay red.
Focused Rust tests pin normalization and collision rejection. The available
pure-Simple release binary still hits the already-tracked lexer SIGSEGV, so its
source-level parity assertions remain staged.
