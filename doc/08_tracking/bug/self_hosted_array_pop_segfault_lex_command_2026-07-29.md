# Self-hosted CLI binary segfaults in spl_array_pop during `lex` (and native-build/compile)

**Date:** 2026-07-29
**Severity:** high — blocks the WM gate, smoke matrix, and guard-channel work; the
freshest pure-Simple self-hosted binary is unusable for any subcommand that does
real work
**Status:** OPEN
**Component:** `src/compiler/10.frontend/core/lexer_struct.spl` (`CoreLexer.scan_token`),
runtime `rt_array_pop` / `spl_array_pop`

## Symptom

`/home/ormastes/dev/pub/simple_wt_secfix/release/x86_64-unknown-linux-gnu/simple`
(sha256 `04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`, built
2026-07-28 21:37:16 UTC, byte-identical to copies in `simple-redeploy-wt`,
`simple-stage4-wt`, `simple_wt_fable`) is genuinely pure-Simple lineage (0 Rust
`_ZN` symbols, 0 `cargo/registry` strings, 20192 unmangled module-qualified
symbols such as `cli__*`/`backend__*`) but segfaults on every subcommand that
does real work:

- `native-build` (both `--backend cranelift` and `--backend llvm`) on a
  trivial `fn main(): print("hi")` — segfault, exit 139, before any output.
- `compile` — fails with "compile bridge exited early before reporting
  diagnostics".
- `lex <file.spl>` — prints all tokens correctly, THEN segfaults (exit 139)
  right after the last token.
- bare `simple <file.spl>` invocation — returns `missing command` instead of
  running the file, indicating the CLI dispatch table itself differs from a
  normal full build.

## Reproduction (PROVED)

```
BIN=/home/ormastes/dev/pub/simple_wt_secfix/release/x86_64-unknown-linux-gnu/simple
"$BIN" lex some_file.spl > out.txt 2>&1; echo exit=$?
# -> prints correct token list, then: Segmentation fault (core dumped), exit=139
```

## Stack trace (PROVED, via `gdb -batch -ex run -ex bt -ex "bt full" --args`)

```
Program received signal SIGSEGV, Segmentation fault.
0x0000000002af57e9 in spl_array_pop ()
#0  spl_array_pop ()
#1  rt_array_pop ()
#2  0x0000000003325530 in ?? ()      <- no symbol; not inside any mapped code
                                         range per `nm` (highest symbol < this
                                         address) — most likely a stale/garbage
                                         stack slot picked up by gdb's
                                         frame-pointer-less unwinder, not a
                                         real call frame
#3  frontend__core__lexer_struct__CoreLexer_dot_scan_token ()
#4  frontend.core.lexer_struct.core_lexer_next_token ()
#5  io___CliCommands__run_commands__cli_run_lex ()
#6  cli___CliMain__args_and_os_commands__run_lex_command ()
#7  cli___CliMain__main_and_help__main ()
#8  spl_main ()
#9  main ()
```

Registers at fault: `rax=0x3325530`, `rbx=0x3325531` (differ by exactly 1 —
looks like the fault address itself, or something derived from it, ended up in
two registers one bit apart), `rdi=0x33254b1`, `rsi=0x3325531`, `r15=0x3325531`
— all clustered in the same ~0x3325xxx region, consistent with a corrupted or
misinterpreted array/heap pointer being handed to `spl_array_pop` rather than a
valid `Array<i64>` object.

**This is NOT a shutdown/atexit crash.** The fault is mid-command, inside the
`lex` subcommand's own token loop (frame #4/#5/#6 walk straight up through
`cli_run_lex` → CLI `main` → `spl_main` → `main`, no destructor/exit-handler
frames). The "prints everything then crashes" signature is explained by the
call site: `CoreLexer.scan_token()` prints/emits each real token as it scans,
and only calls `self.indent_stack.pop()` (to close out remaining indentation)
on the **final** call, once `self.at_end()` is true
(`src/compiler/10.frontend/core/lexer_struct.spl:1067-1076`, guarded by
`if slen > 1: self.indent_stack.pop()`).

## Source-state check (PROVED — not a stale-snapshot artifact)

```
cd simple_wt_secfix && git status --porcelain      # -> empty, clean
git log --oneline -5
  7d2c7fd1cff 2026-07-28 23:08:42  chore: preserve stale Claude worktree simple_wt_secfix
  36fc2ce69f9 2026-07-28 21:36:19  docs(llm-caret): land agent-teams and embedded-tmux docs plus 2 system specs
  4dc44e1a110 2026-07-28 21:32:07  feat(codegen): default-off diagnostic for receiver-type-blind bare-method binds
  9fa3141e97b 2026-07-28 21:31:15  feat(linker): fabricated-stub ratchet at the Rust emission site
  69b91e581   2026-07-28 21:30:17  fix(web-renderer): make hand-rolled scanners byte-indexed, not character-indexed
```

The binary (finished building 21:37:16) was built from commit `36fc2ce69f9`
(21:36:19, ~1 minute before the build completed — consistent with link+copy
time), which was HEAD at the time. The tree was clean; there is no
uncommitted/mid-edit state to blame. The later `7d2c7fd1cff` (23:08:42) landed
**after** the build and only swept in unrelated `.cargo-target-secfix/**` and
`tauri-shell/**/gradlew.bat` artifacts — it did not touch source and is not
causally related.

`4dc44e1a110` ("default-off diagnostic for receiver-type-blind bare-method
binds", landed 21:32:07, 4 minutes before build completion) was checked and
ruled out: it only adds an opt-in `eprintln!` diagnostic
(`SIMPLE_DEBUG_ERASED_RECEIVER_BIND`) behind an env-var gate in
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`, and its own
commit message documents a proof that patched-on/patched-off/control builds
produce byte-identical archives for a fixture — i.e. it is a report-only change
with proven zero behavior impact.

Commit `8d1d0a4476c` (the fix this session was originally verifying) is
confirmed an ancestor of `36fc2ce69f9` (`git merge-base --is-ancestor` exit 0).

## Verdict: (c) — miscompilation, most likely a sibling instance of the already-tracked, open codegen defect

This is not (a) a stale-snapshot artifact (tree was clean, commit identified,
nothing suspicious in the interval) and not (b) a shutdown-path bug (crash is
mid-command, not at exit).

The strongest lead is `doc/08_tracking/bug/codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28.md`
(OPEN, filed the same day): bare method calls on a receiver whose static type
is erased at the call site get bound to whatever `Type_dot_<method>` symbol
happens to be linked into the entry closure, by name-suffix alone, with no
receiver-type check. That doc explicitly documents `push` (a sibling `Array`
mutator) as a confirmed "THEFT" victim (`RingWindow.push`, found via reloc
census over the `gui_entry_desktop` closure) and states in its own words: "the
set is neither small nor closed... each additional closure keeps adding new
tuples." **`pop` is not yet in that doc's known-victims table.**

I checked `is_bare_builtin_collection_method` in
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:113-166` —
the allowlist that routes known-hazardous bare method names to safe
tag-dispatching `rt_*` builtins before name-suffix resolution runs. Its exact
member set is: `get`(1), `has`/`contains`/`contains_key`/`has_key`(1),
`remove`(1), `find`(1), `starts_with`/`ends_with`(1), `slice`(1|2|3),
`len`/`length`/`keys`/`values`/`is_empty`(0). **`pop` is absent from this
list.** Separately, `"pop" => "rt_array_pop"` exists in the codegen's
normal/typed builtin-method table (line ~1260) — the path used when the
receiver's type IS known — so a **statically-typed** `Array<i64>.pop()` call
(such as `self.indent_stack.pop()`, a struct field of declared type
`Array<i64>`) should route there directly and correctly, matching what frame
#0/#1 of the backtrace show (`spl_array_pop`/`rt_array_pop` were in fact
reached).

**What I could not fully prove (INFERRED, not verified at the object-code
level for this exact binary):** whether the crash is (i) `spl_array_pop`
correctly invoked but operating on an `indent_stack` array object whose memory
was already corrupted earlier in the same process by an *unrelated* bare-method
mis-bind elsewhere in the linked closure (the open bug's own numbers — 97
erased-receiver binds, 22 distinct method names, in one SimpleOS closure alone
— make this plausible: `push`, `to_i64`, `unwrap` and others are confirmed
thieves in-tree, and `self.indent_stack.push(...)` /
`self.force_indent_bracket_depths.push(...)` are both called earlier in the
same lexer), or (ii) a genuine, independent bug inside `spl_array_pop`'s own
runtime implementation (bounds/length handling) that is unrelated to the
erased-receiver class. I attempted to settle this by rebuilding
`src/app/cli/main.spl` with `SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1` and
`--entry-closure` to get a direct census, but the full CLI closure fails to
parse at discovery time (`src/os/compositor/host_compositor_core.spl:699:50`,
unrelated syntax error, pre-existing in that closure) before it reaches
codegen, so no direct confirmation was obtained in the time available.

## Recommended next step (not applied — validation cost is non-trivial)

Given the sibling defect (`push`) is a confirmed victim of the same class,
the cheapest next diagnostic step is exactly the one the existing bug doc's
"Suggested next steps" already prescribes: extend the
`SIMPLE_DEBUG_ERASED_RECEIVER_BIND` census (already landed, default-off, proven
zero-behavior-impact) to a closure that actually parses cleanly and includes
`src/compiler/10.frontend/core/lexer_struct.spl`, and check whether `pop` shows
up as an erased-receiver bind anywhere in it. If it does, the fix is the same
one-line shape as `8d1d0a4476c`/`bea738bdb0b`: add `pop` (and by extension
`push`, already known-vulnerable) to `is_bare_builtin_collection_method`,
verified with the same byte-identical-archive proof protocol, then a full
bootstrap. That is a real Rust-seed change requiring full-bootstrap validation
before landing — not attempted here per the "fix only if trivially small"
guidance, since validation cost is not trivial even though the code delta
likely is.

## Impact

Blocks: WM gate, smoke matrix, and the three guard-channel checks queued
behind a working pure-Simple binary. **Do not deploy this artifact** (or its
byte-identical copies in `simple-redeploy-wt`, `simple-stage4-wt`,
`simple_wt_fable`) as the production `bin/simple`.

## Related

- `doc/08_tracking/bug/codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28.md` — the open, broader defect class this is most likely a sibling instance of.
- `8d1d0a4476c` — narrow fix for `starts_with`/`ends_with` (verified present in the currently-deployed Rust seed via `objdump -r` reloc check).
- `4dc44e1a110` — landed the `SIMPLE_DEBUG_ERASED_RECEIVER_BIND` diagnostic; checked and ruled out as the cause of this crash (proven zero-behavior-impact by its own commit).
