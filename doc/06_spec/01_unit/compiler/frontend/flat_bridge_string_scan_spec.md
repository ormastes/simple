# Flat-Bridge String Scan Specification

Ordinary non-raw string literals without braces bypass interpolation parsing and
brace decoding, returning the parser-owned text unchanged. Brace-bearing text
still follows the existing interpolation parser, while plain doubled braces are
decoded left-to-right with exact historical output.

The executable fixture pins empty and ordinary strings, `{{`, `}}`, odd/mixed
and consecutive escape runs, and unmatched braces. It directly inspects two
identifier placeholders in order, a valid nested-brace binary string expression,
invalid fragment fallback, and an unclosed region. Static source boundaries require the
ordinary-literal and no-escape identity paths, one final decoder join, and one
interpolation-fragment join. They reject the former growing immutable prefixes.

For literal bytes S and interpolation payload K, ordinary no-brace conversion
now performs bounded membership scans without output allocation; escaped plain
text is O(S) scan/copy work with O(number of escape runs) fragments; an actual
interpolation payload is assembled in O(K) copied bytes rather than O(K²)
cumulative prefix copying. The existing parser, expression order, raw-string
bypass, invalid-fragment fallback, and MIR ownership are unchanged.

No compiler, test, optimizer, timing, allocation, or RSS execution was performed
under the user override.
