# CLI entry and configured stdin pipe exports

The completed early Phase4 log, SHA-256
`0850b659da9f5a612051ed073f9062414329818219bce1f96c3f044b6be01340`,
reports missing `t32_cli_main` from `app.t32_cli.mod` and missing
`stdin_read_line` from `std.io` in both TUI input entry modules.

`src/app/t32_cli` is a tracked alias to the example TRACE32 CLI. Its canonical
module defines the entry function but does not explicitly export it. Export
that entry at the canonical source; do not replace the materialized alias.

The no-GC sync pipe owner already defines the optional-text stdin reader and
terminal wrappers. The no-GC async pipe facade exports only the three stream
types; GC families reexport that facade. Carry the existing wrappers through
that facade and import `std.io.pipe` in the consumers, retaining configured
family selection. Bind the optional reader result with `if val` before trimming;
a nil comparison alone does not narrow an optional value in this compiler.
EOF continues to return empty text, as does an empty or whitespace-only line.

Two executable unit scenarios exercise the exported CLI through help, unknown
command, and exit-state reset, without requesting a TRACE32 connection.
Two native stdin fixtures exercise the actual TUI app and input wrappers.
Run each compiled fixture with one expected-value argument and these stdin bytes:

| Input bytes | Expected argument |
|---|---|
| `  trimmed  \n` | `trimmed` |
| `\n` | empty text |
| zero bytes, closed stdin (EOF) | empty text |
| `\t  \r\n` | empty text |

Each fixture requires exit zero and stdout `stdin-owner-pass\n`. Compile/run
both fixtures under each supported configured family to validate the facade
chain. All native scenarios are UNRUN pending repaired compiler verification;
source checks do not establish a passing bootstrap or release qualification.
