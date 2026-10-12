# Block parser and highlighting owner contracts erased by source corruption

Status: source repair authored; native qualification pending.

The frozen attempt 5 stage2 native build failed on two independent block utilities.
Evidence: `C:/dev/simple-phase3-attempt5/build/bootstrap/logs/x86_64-pc-windows-msvc/stage2-native-build.log`.

* `highlighting.spl:39` loaded an undeclared `has_index` global after calling
  `text_index_of`. The surrounding file also referenced absent `text_len`,
  `has_block_comment`, and `block_comment_value` helpers/bindings.
* `testing.spl` could not project `error.message` in `test_parse`: its matched
  payload was `ANY`. `BlockDefinition.parse_payload` declared a `text` result
  despite concrete built-ins returning `Result<BlockValue, BlockError>`.
  Simple/mock/full builder callback slots and adapter return signatures were
  likewise erased to `text`; the required builder parser additionally declared
  `Option<Result<...>>` although it always returns `Ok` or `Err` directly.

Repair commit `1eab5e3ffdc459097e269bd0743dec3f84262896` restores the actual owner
contracts. Keyword search uses the native signed index sentinel before token
construction, Optional comment delimiters are bound with `Some`, and text length
uses the existing text method. Parser traits and full callbacks preserve
`Result<BlockValue, BlockError>`; simple callbacks preserve
`Result<BlockValue, text>` and adapters convert text errors to `BlockError`.
The registry returns `BlockDefinition?` and testing unwraps `Some`/`None`.
The foreign plugin adapter wraps its existing successful text handle as
`Ok(BlockValue.Raw(...))`, retaining its null-handle panic.

Testing also imports its actual registry/error helpers, constructs a real
`BlockContext` with the complete payload span, uses declared mock field names,
and retains the existing parser mismatch/failure assertions.

## Regression and evidence boundary

`test/01_unit/compiler/blocks/typed_parser_highlighting_spec.spl` exercises the
real functions, not implementation strings. It checks absent/repeated/whole-word
keyword positions, configured/absent block-comment delimiters, simple/mock and
full builder callback Ok/Err values, retained error spans, registry Optional
ownership, duplicate registration, removal, and testing helper error-message
projections. The full builder has no implemented `build` function in this tree;
the regression therefore invokes its actual `_parser` slot after the real
builder setter APIs, without inventing a builder API or replacement adapter.

Initial external source-contract checks passed 24/24 and `git diff --check`
passed. These are source review evidence only. The semantic regression and
native build have not run; no passing suite, link, or runtime claim is made.
Broader pre-existing optional-hook annotations and trait dispatch remain subject
to actual qualification by the coordinated bootstrap owner.
