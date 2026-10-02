# Windows absolute SCV source selectors

The compile snapshot selector classified only paths starting with `/` as
absolute. A native `C:/checkout/src` selector therefore became
`C:/checkout/C:/checkout/src` before physical canonicalization. The plain
checkout owner already recognizes drive, UNC and verbatim absolute paths.
The patch reuses that owner after the canonical host-path conversion, then
retains physical containment and ignored-cache rejection.

The separate final SCV timing diagnostic published a valid one-row inventory
for a 3058-byte tracked source. Its selector observed one admitted entry, one
requested root, one resolved root and one visited entry, but zero matches.
The actual selector path bytes were not recorded. MSYS environment conversion
is a plausible boundary explanation, not proven as the sole diagnostic cause.

No fourth SCV diagnostic or phase2 qualification was executed. Regression
specs and production checks are **UNRUN**. The change is not a performance fix
or an admission of the preserved LLVM candidate.
