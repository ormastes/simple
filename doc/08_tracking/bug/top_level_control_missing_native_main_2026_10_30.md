# Top-level control flow fails to synthesize native main

Status: source repair prepared; corrected-producer runtime verification pending.

Attempt11 plain MC/DC-off diagnostic compiled the three-line `val`/`if` fixture
through MIR (one module, two functions, 23 instructions, zero fatal findings),
then failed linking with undefined `__simple_main`. The generated source object
defines only the guarded dynamic initializer and global initialization wrapper;
`simple_entry.o` calls that initializer and the absent `__simple_main`.
Retained object paths, hashes and symbols are recorded in
`/tmp/plain-mcdc-off2-missing-entry-symbol-audit-20261030.txt`; the original log is
`/tmp/simple-phase2-runner-native-attempt11-20261030/plain-mcdc-off2/direct-diagnostic/build.log`.

The parser encodes top-level `if`, `for` and `while` as generated value
declarations. Their `_if_`, `_for_` and `_while_` prefixes did not match the
bridge's existing `_expr_` convention, so those statements alone never triggered
synthetic main. Use `_expr_if_`, `_expr_for_` and `_expr_while_` for these
parser-generated declarations. Keep the bridge unchanged: authored bindings
with the former prefixes remain bindings, and an explicit main still receives
the original module-initializer behavior.

Regression spec: `test/01_unit/compiler/frontend/top_level_control_synthetic_main_spec.spl`.
Native fixtures: `test/fixtures/compiler/top_level_control_main/`.
Required observed results: `if_green` exits zero; `if_red` exits nonzero with
`EXPECTED_TOP_LEVEL_IF_FAILURE`; `for` and `while` each print `1`, `2`, `3`, each
followed by LF and exit zero; `explicit_main` exits 42. These are authored
expectations, not executed PASS claims. Verify with a producer containing this
parser repair; compiling fixtures with an unchanged producer repeats the bug.
