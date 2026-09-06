# yaml parse: single-quoted scalars and nested block mappings

**Status:** FIXED — found 2026-08-01 while fixing
`common_encoding_yaml_broken_cross_submodule_import_2026-07-20`, fixed
2026-08-01 in `src/lib/common/yaml/parse.spl`.

Two pre-existing defects in `src/lib/common/yaml/parse.spl`, distinct from the
import/tag bug and left unfixed there on purpose: they are in a different file
and fixing them would have widened that change's blast radius past what its
numbers covered.

They were the only 2 remaining failures out of 27 in the yaml spec once the
import and scalar-tag defects were fixed (0 of 27 executing -> 25 pass / 2 fail
-> 27 pass / 0 fail).

## 1. `parse_single_quoted` — single quotes are never stripped — FIXED

`yaml_parse_scalar` (`parse.spl:51-52`) stripped only `"` quotes. A
single-quoted YAML scalar kept its quotes in the parsed value.

YAML 1.2 treats `'...'` as a flow scalar with `''` as the escape for a literal
quote, so this was not a formatting nicety — `'it''s'` round-tripped wrong.

**Fix:** `yaml_parse_scalar` now recognises the `'...'` form after the `"..."`
form and unescapes `''` to `'`. There are deliberately no backslash escapes in
the single-quoted branch — YAML 1.2 does not define any there.

## 2. `parse_nested_count` — indented nested mappings are not folded — FIXED

Expected 1 top-level entry, got 3: the block parser split every line on `:` in
one flat pass, so indented child mappings were emitted as siblings of their
parent. Any non-flat YAML document parsed to the wrong shape.

**Fix:** `yaml_parse_block`'s mapping branch is now indentation-aware. Two new
helpers, `_yaml_indent_of` (leading space/tab byte count) and `_yaml_dedent`
(re-join a line range with N leading whitespace bytes removed), let a key whose
value is empty claim the following deeper-indented run as its nested block; that
run is dedented and re-parsed by `yaml_parse_block` recursively, so nesting works
to arbitrary depth and a nested *sequence* under a key works too. Blank lines no
longer terminate a nested block and no longer emit a pair.

The same rewrite also fixed a latent truncation: the value is now everything
after the **first** colon, where the old `kv[1]`-only read silently dropped
anything past a second colon (`url: http://example.com/x` parsed as `http`).

The block *sequence* branch is unchanged — nesting under `- ` is still flat and
is out of scope here.

## Evidence

Measured with a `run`-based oracle whose helper bodies are byte-identical to
`test/01_unit/lib/common/encoding/yaml_spec.spl` (only the harness differs), on
`src/compiler_rust/target/bootstrap/simple`:

- before: `TOTAL pass=25 fail=2` — `nested_count` got 3 want 1,
  `single_quoted` got `'foo bar'` want `foo bar`. Exactly the two defects above.
- after: `TOTAL pass=27 fail=0`.

Plus a 16-assertion extended probe covering cases the spec does not reach —
`'it''s'` -> `it's`, `''` -> empty, a lone `'` left alone, 3-level nesting,
blank line inside a nested block, nested block sequence under a key, colon in a
value, and a key with an empty value and no children -> null: all 16 pass.

Both probes ran on the tree-walk interpreter (the run emitted the
`unresolved external symbol 'yaml_serialize_block'` JIT-fallback notice), which
is the same engine `simple test` uses — so the numbers transfer to the spec
runner. `simple test` was not used for authoritative numbers: it exceeded 300s
on a loaded box, and it silently delegates to the Rust seed child.

Unaffected neighbours checked by inspection: `yaml_flow_guard_spec.spl` (flow
paths only), and the `yaml_parse` block assertions in `yaml_coverage_spec.spl` /
`parsers_misc_coverage_spec.spl` (flat two-key mapping and flat sequence, both
covered by the oracle).
