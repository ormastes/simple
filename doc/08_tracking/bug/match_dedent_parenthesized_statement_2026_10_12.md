# Match DEDENT consumes the following parenthesized statement

Bug: `BUG-MATCH-DEDENT-CALL-20261012`.

Status: current pure-Simple parser source repaired and four actual parser/bridge
criteria passed in the reviewed confined source runner. Repaired native compiler
integration remains UNRUN. Frozen object-build sources remain unchanged.

## Failure and authentic AST evidence

An authored `val available = match ...` followed by
`(required.feature_mask & available.feature_mask) == required.feature_mask`
fails native HIR with `unresolved name: available`. The match arm parser consumes
its DEDENT, leaving the following statement's opening parenthesis current.
`parse_postfix` then treats that parenthesis as a call on the completed match.

The retained pure-Simple producer
`f2ce31b4e4dea1ea6ca3e8726cd411144914c24ffcf58722021f38c4b6393dec`
reproduced the failure in the minimal source at `main.spl:21:30`. Its authentic
frontend cache has verified source and payload SHA256 checksums. The `required`
initializer is EXPR_MATCH node28; the `available` initializer is EXPR_BINARY
node52, whose left49 is EXPR_CALL with EXPR_MATCH callee40. The parenthesized
result was swallowed into the initializer before `available` could be bound.

The original registry owner is identical in frozen, current and committed
ab9a782 source. That committed parser also lacks this boundary guard.
The Rust parser's postfix source checks token adjacency before LPAREN calls;
no Rust seed execution was used for the native reproduction.

## Repair and regression criteria

The pure-Simple postfix parser records its primary token kind and line. If the
primary began with MATCH, produced EXPR_MATCH and now sees LPAREN on a later
line, it returns the completed match. An explicitly parenthesized match starts
with LPAREN and retains postfix calls. General call whitespace rules, frozen
cache identities and native entry behavior are unchanged.

`test/01_unit/compiler/frontend/match_statement_boundary_spec.spl` uses the real
flat parser and bridge to assert:

- A match initializer and following binary result remain two statements.
- Two match bindings and the binary result remain three statements.
- An explicitly parenthesized match remains a call target with one argument.
- An ordinary adjacent call retains its named target and one argument.

## Qualification and limits

The feature used three cycles. Cycle1 was the native RED reproduction and
retained AST proof. Cycle2 was a harness mismatch: the newer frozen parser
required `expr_set_call_type_args`, absent from the older confined dependency
snapshot. Its two failures are not an AST baseline verdict.

Cycle3 restored the internally consistent current parser owner and applied the
boundary guard. The d958 confined runner executed four criteria: 4 PASS, 0 FAIL,
exit0, finalJob0; 1,614 traced reads stayed within the private source snapshot,
all 19,245 source pins remained unchanged, and peak RSS was 437,796 KiB. The two
positive controls ran only in cycle3. No green checks were repeated.

Baseline owner SHA256:
`9717d1948df5e4145dbf530f234ff848e01a93ad4e823a30825f5e5b46a7d742`.
Tested candidate SHA256:
`9731c37f5e82a0c9ebf6bb2ff3ea0f3b374a5798a2abb976eb678825626a6c6d`.
The applied source has LF-normalized SHA256
`4e26d97ba8a4e241d3a2af81d18f1eb0013daed3ea6dff5ce212ca47f9583ac6`;
its normalized content matches the tested candidate.

Evidence packet:
`build/native_probe/match-local-parenthesis-20261012-astra/`.
`FINAL_EVIDENCE.json` binds source, manifests, logs and receipts;
`RETAINED_AST.json` records the authentic failing AST.
Cycle3 receipt: `confined/candidate/attempt/receipt.env`, SHA256
`07fd5b76ec1e5d7203408e0072538fe8bacb7b4897acf1a7cf1643c052bf492d`.

This qualifies the current-source parser repair in a confined source diagnostic.
It does not qualify a repaired native compiler, the separately mapped frozen or
ab9a782 candidates, or any Phase3/Phase4 product. A later admitted repaired
producer must compile the native regression fixture to establish that result.
The three-cycle limit is closed; no fourth run or unchanged failed-module replay.
