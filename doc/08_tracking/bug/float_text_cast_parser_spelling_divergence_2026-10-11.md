# Canonical float parser and legacy builtin accept different spellings

Status: open language/parser parity issue; canonical bug-index reconciliation
pending a qualified bug database tool.

`src/runtime/simple_core/core_string.spl::rt_string_to_float` and its existing
runtime twin use `strtod`, permit surrounding whitespace, and accept C
hexadecimal float spellings. The legacy builtin implementation in
`src/compiler_rust/compiler/src/interpreter_call/builtins.rs` parses text with
Rust's `str::parse::<f64>()`, which rejects those spellings.

Concrete probes requiring a shared language decision and executable parity
coverage are `float(" 1.25 ")` and `float("0x1p2")`. The canonical parser
accepts these as 1.25 and 4.0; the legacy builtin rejects them. These are
source-contract observations, not completed cross-engine execution evidence.
Ordinary decimal/exponent text should continue parsing, and empty text,
trailing junk and nonnumeric text must continue failing.

The pointer-to-double MIR repair deliberately uses the existing canonical
parser with explicit nil rejection, as authorized for that repair lane. It
does not alter runtime parser code, fall back to numeric pointer addresses,
return a fabricated zero, or claim this spelling discrepancy is resolved.
