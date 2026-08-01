# yaml parse: single-quoted scalars and nested block mappings

**Status:** OPEN — found 2026-08-01 while fixing
`common_encoding_yaml_broken_cross_submodule_import_2026-07-20`.

Two pre-existing defects in `src/lib/common/yaml/parse.spl`, distinct from the
import/tag bug and left unfixed there on purpose: they are in a different file
and fixing them would have widened that change's blast radius past what its
numbers covered.

They are the only 2 remaining failures out of 27 in the yaml spec once the
import and scalar-tag defects are fixed (0 of 27 executing -> 25 pass / 2 fail).

## 1. `parse_single_quoted` — single quotes are never stripped

`yaml_parse_scalar` (`parse.spl:51-52`) strips only `"` quotes. A single-quoted
YAML scalar keeps its quotes in the parsed value.

YAML 1.2 treats `'...'` as a flow scalar with `''` as the escape for a literal
quote, so this is not a formatting nicety — `'it''s'` currently round-trips
wrong.

## 2. `parse_nested_count` — indented nested mappings are not folded

Expected 1 top-level entry, got 3: the block parser emits indented child
mappings as siblings of their parent instead of nesting them.

This makes any non-flat YAML document parse to the wrong shape, which is a
larger correctness problem than #1 and is likely the more urgent of the two.

## Evidence

Measured with a `run`-based oracle whose 201 lines of helper bodies are
byte-identical to `test/01_unit/lib/common/encoding/yaml_spec.spl` (diff showed
only the harness differs). `simple test` could not be used for authoritative
numbers — it exceeded 300s and then 2400s on a box under load ~68.
