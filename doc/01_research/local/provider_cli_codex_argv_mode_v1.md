# Exact Codex argument prompt evidence

Research only; actual agent/task execution was not performed. Existing installed
read-only captures identify `codex-cli 0.169.0`, root exec positional PROMPT and
resume SESSION_ID/PROMPT. Captures remain under
`/tmp/caret-provider-cli-probes-20261115-sol`. No version/help command was rerun.

Official source was read with the connected GitHub file API at the exact release:

| Source | Git blob |
|---|---|
| [Codex exec CLI](https://github.com/openai/codex/blob/rust-v0.169.0/codex-rs/exec/src/cli.rs) | `5ada863143608639c9f538c7ada72b531561b474` |
| [Codex exec prompt handling](https://github.com/openai/codex/blob/rust-v0.169.0/codex-rs/exec/src/lib.rs) | `bb01fc3568e06be44343d79df1312259f76bddbd` |
| [Codex Cargo.lock](https://github.com/openai/codex/blob/rust-v0.169.0/codex-rs/Cargo.lock) | `d719a520b78e32c58f4ccc5581a527044a368d6f` |
| [Pinned Clap parser](https://github.com/clap-rs/clap/blob/v4.5.58/clap_builder/src/parser/parser.rs) | `64135f5212e86697b8f38fa1a0a8aac98fb4623d` |
| [Pinned Clap argument lexer](https://github.com/clap-rs/clap/blob/v4.5.58/clap_lex/src/lib.rs) | `6ba028a6d7a665114059de6e71bbfa9b594940d6` |

The CLI declares a positional prompt at 86–90, and resume's separate prompt at
237–239. Cargo.lock pins Clap 4.5.58. Its lexer recognizes exactly `--` as the
option terminator (307–309); the parser switches to trailing positional values
(130–145). The Codex prompt arguments do not enable hyphen-valued option parsing.
An explicit terminator followed by the prompt therefore prevents flag/subcommand
interpretation, including prompts beginning with `-`, `--`, or `resume`.

Codex `resolve_prompt` at 2526–2540 treats exactly `-` as the stdin sentinel; even
an option delimiter cannot make it a literal argument prompt. Argument mode must
refuse that text rather than modify it. Resume calls that resolver at 991–1003.
Root Start uses `resolve_root_prompt`: a non-sentinel argument can still append
piped stdin at 2543–2553. The reader checks terminal status and uses `read_to_end`
at 2470–2492. Actual closed-stdin/non-TTY engine configuration is therefore a
pre-first-start requirement for this noninteractive profile. Request terminal-mode
DATA, a successful write, revocation or transport cleanup does not prove that fact.

These sources and local help establish version-specific planning semantics, not
vendor provenance, contained image compatibility, credentials or native admission.
Actual contained selection and immutable image/program/scope binding remain in
their existing owners. The new pure mode does not authorize Resume store/history.
