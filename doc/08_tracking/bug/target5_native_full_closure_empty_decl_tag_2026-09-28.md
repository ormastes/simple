# Native full-closure parse reports empty declaration tags

Status: open; blocks Target 5 full CLI Stage4 link and size qualification.

The Target 5 diagnostic pure-Simple compiler compiled 959 source units, then
attempted `src/app/cli/main.spl` with entry closure across compiler, app,
lib, and plugins. Source closure resolved 2,446 files. Parsing began, but
`flat_ast_to_module` repeatedly reported `unhandled decl node kind (tag=)`.
The first error context was
`src/app/cli/_CliMain/args_and_os_commands.spl` at EOF line 452, lexer kind
190, with an empty declaration tag. Many unrelated modules later failed the
same way, so the evidence does not identify that source file as defective.

An initial retry reached about 17,275,068 KiB peak RSS and exited after
about 78 seconds before link selection. A final bounded retry with
`SIMPLE_NATIVE_ARENA_DECLS=1`, a 12 GB address-space cap, and a 120-second
timeout still failed in the bridge; it exited after 34.69 seconds with
5,580,064 KiB peak RSS. The native arena flag reduced memory pressure but
did not resolve the parser state.

The bridge obtains `raw_decl_count` from `module_decl_count_get()`, then each
index from `module_decl_at()` and each tag from `decl_get_tag()`. An empty tag
means the declaration index/tag lookup needs investigation. In particular,
test `ast_module_decl_slot_push()` and the arena reset/restore path in a
small native reproducer before changing parser dispatch. This is a hypothesis,
not a proven root cause. Do not suppress the bridge diagnostic or treat EOF
as a valid declaration to make the full CLI build pass.

The session reached its three full CLI verify/fix attempts. The next run
should start from an isolated reproducer and only retry the full CLI after
the declaration lookup has a native regression test.
