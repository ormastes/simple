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

## Focused native reproducer

`test/02_integration/compiler/ast_module_decl_slots_native_probe_main.spl`
compiled 48 source units with the admitted Stage2 pure-Simple compiler. It
clears the module-declaration arena, appends indices 7 and 11, and reads
both direct and wrapper accessors. With or without
`SIMPLE_NATIVE_ARENA_DECLS=1`, it reports count 2 and slots 2. Direct slot
reads return 7 and 11, but `module_decl_at(0)` and `(1)` both return -1. The
probe exits 1 until that wrapper path is repaired. Splitting its combined
bounds condition into two `if` statements did not change the result; that
trial edit was reverted. Native disassembly shows the first count check is a
direct `cmp index,count; b.ge` and passes. In the native-arena branch, the
`index >= ast_module_decl_slots_len()` expression calls a comparison helper,
then emits `cmp x0,#0; b.ge` before the `-1` return. If the helper returns a
normal boolean 0 or 1, that signed `b.ge` is always taken. This is direct
code-generation evidence for the wrapper's false rejection, although the
precise helper ABI still needs a targeted check. The candidate below removes
that cross-module comparison; retain invalid-index rejection in the native
regression spec.

## 2026-09-29 owner-side candidate

The candidate moves the slot bounds check into `decl_nodes.spl`, next to the
`module_decl_slots` array, and has `module_decl_at` call that checked accessor.
The existing native probe now also checks the negative index. This removes
the cross-module `index >= ast_module_decl_slots_len()` comparison identified
above while preserving the count check and both out-of-range cases.

A 3-unit native probe built with the staged pure-Simple compiler and passed
valid and invalid indices in both arena and default environments. Its direct
cross-module comparison also passed, so this small probe does **not** reproduce
the full-closure miscompile and cannot qualify the candidate. The original
48-unit native probe build using the installed Rust bootstrap seed failed in
JIT setup on missing `rt_file_read_regular_no_follow_bounded_bytes`; it did
not reach the probe. A staged pure-Simple compiler attempt with the broad
`src/compiler` and `src/lib` roots was terminated after about one minute when
its RSS reached about 40 GiB, without producing a binary. The 48-unit native
probe and full CLI remain unverified. Narrow closure construction or a current
bounded self-hosted compiler is needed before this bug can be closed.
