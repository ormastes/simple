# Feature Documentation Parser Block Assembly Specification

Source: `test/01_unit/app/feature_doc_parser_spec.spl`

## Contract

Triple-quoted feature documentation preserves raw interior lines and blank-line
multiplicity, then performs the historical whole-block trim. Empty closed blocks
remain represented, closing delimiters remain excluded, and unterminated blocks
remain silently discarded. Title, metadata, describe, and context association
consume the same resulting text.

The parser stores line references in encounter order and joins them once after a
closing delimiter. It must not repeatedly concatenate the growing text prefix.
Pure Simple and C-native join implementations use a length pass and one exact
output allocation. The legacy Rust seed exposes multiple join entrypoints with
different algorithms, so this specification makes no exact seed-runtime
allocation or scaling claim without route-specific execution evidence.

## Executable scenarios

The executable spec covers empty and multiline blocks, boundary and interior
blank lines, indentation, metadata/title extraction, nested describe/context association,
unterminated EOF behavior, and the single-join source contract. It was added but
not executed under the user's no-verification instruction.
