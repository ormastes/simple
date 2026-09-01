<!-- codex-requirements -->

# Lazy system path variables

## Selected behavior

- **REQ-LSPV-001:** A path template may contain registered `{sys:<name>}` references. Unknown names, malformed braces, and relative override roots fail with a typed error.
- **REQ-LSPV-002:** Construction is inert: it performs no environment lookup, platform query, filesystem access, allocation proportional to the environment, daemon launch, or database access.
- **REQ-LSPV-003:** First resolution uses precedence: explicit application override, registered application environment override, `SIMPLE_SYS_*` override, operating-system standard variable, platform fallback.
- **REQ-LSPV-004:** `{sys:compiler_cache}` uses `SIMPLE_CACHE`, then `{sys:user_cache}/simple/cache-manager`.
- **REQ-LSPV-005:** Logical output uses UTF-8 `/` on Windows and Unix. Stable
  cache values use `C:/...`; the documented MinGW/MSYS `/c/...` spelling is an
  admitted boundary input and converts to the same drive path.
- **REQ-LSPV-006:** A resolved template memoizes either its successful value or error for deterministic repeated access. Tests may use a non-process input record.
- **REQ-LSPV-007:** Raw strings never perform ordinary Simple interpolation. The library constructor accepts raw template text; future `_path` and contextual-`Path` lowering shall compile `{sys:...}` directly into deferred tokens.
- **REQ-LSPV-008:** Passing runtime `text` to a strong `Path` API eventually becomes an error after migration; literals in an expected `Path` context may lower contextually without `_path`.
- **REQ-LSPV-009:** The pure-Simple parser, interpreter, and native frontend shall eventually have parity for typed string suffixes before `_path` is the default spelling.
- **REQ-LSPV-010:** Canonical values remain `/`-separated, but file access and executable launch convert at the final host boundary. Windows, MinGW, MSYS, and Cygwin accept `C:/x`, `/c/x`, and `c/x`, pass `C:\\x` to the OS, and preserve UNC roots as `\\server\share`.
