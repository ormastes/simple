# Lane IFCHAIN — same-indent leading `-`/`+` swallowed as a binary operator

**Date:** 2026-07-28 · **Status:** root-caused, fix sketched, NOT applied (crate contended)

## Verdict on the incoming report

TLSVER's framing — "the last arm of a long single-line if-chain returns the
PREVIOUS arm's value" — is **wrong in its diagnosis but right about the damage**.
`if` is innocent. Chain length is irrelevant. The swallowed token is the bare
`-1` sentinel *tail*: `return 15` ⏎ `-1` parses as `return (15 - 1)`.

`15` ⏎ `-1` in a bare function body, with no `if` anywhere, yields 14.

## Root cause

`src/compiler_rust/parser/src/expressions/binary.rs:68-90` ("Case 2", leading
line-continuation) calls `peek_through_newlines_and_indents`
(`src/compiler_rust/parser/src/parser_helpers.rs:408-438`), which walks over
`Newline`/`Indent` and stops only at `Dedent`/`Eof` — **it never compares
indentation**. A same-indent next line emits a bare `Newline`, so the lookahead
finds the `-` and takes it as binary subtraction.

Rust seed only. `src/compiler/10.frontend/core/parser_expr.spl:377-391`
(pure-Simple) has no newline peeking → **seed vs self-hosted semantic divergence**.

## Deliverables

- `doc/08_tracking/bug/if_chain_last_arm_returns_previous_value_2026-07-28.md`
  — truth table (17 rows, both engines), mechanism, fix sketch, blast radius
- `test/01_unit/compiler/if_chain_arm_value_spec.spl` — regression gate; lint 0 errors
- `build/ifchain_repro/` — per-case repros (`case_*.spl`), `matrix.txt`,
  `hazard2.txt` / `hazard_minus.txt` (blast-radius scan output)

## Trigger boundary

Glues iff: next line's first token is `+`/`-` AND no `DEDENT` between the lines
(same-or-greater indent) AND the previous statement ends in a value expression.
Blank lines do not stop it. `(-1)`, `return -1`, an unsigned literal, or a
dedent all avoid it. Deeper-indent leading operators are the *intended* feature
and must be preserved.

## Fix (not applied)

Add an indent-requiring lookahead variant; use it in all three Case-2 copies
(`binary.rs:21-25`, `:68-90`, `:142-146`). Leave the leading-`.` method-chain
path alone.

**Blocked on:** `src/compiler_rust/parser/` has a live lane
(`src/lexer/strings.rs`, `src/fstring_bug_tests.rs` both dirty). Landing here
would force a seed rebuild on top of in-flight lexer work. Handed over as a
sketch per lane rules.

## Blast radius

156 sites in owned `src/` + `test/` (142 of the `-` form). Worst: ~20 hex-nibble
decoders that decode every `f`/`F` as 14 — including
`src/os/kernel/net/embedded_certs.spl:32` (kernel TLS trust anchors),
`src/lib/common/js/builtins/number.spl:432` (`parseInt` radix path),
`src/lib/nogc_sync_mut/web_framework/auth_middleware.spl:493`. Second cluster:
~43 `eval_set_error(...)` ⏎ `-1` error sentinels across the pure-Simple
interpreter. Third: ~33 in `src/os/kernel/**`.

Interim guard recommended: a lint rule for statement-leading `+`/`-` at the same
indent — catches all 156 without a seed rebuild.

## Not done

- Did not edit any compiler source (crate contended).
- Did not fix the 156 call sites — they are correct under the pure-Simple
  compiler; rewriting them would paper over the seed defect.
