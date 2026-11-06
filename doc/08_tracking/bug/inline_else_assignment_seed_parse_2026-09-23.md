# Inline else assignment fails in the deployed aarch64 seed

Status: OPEN grammar compatibility bug; AVX2 caller uses block-form assignment.

Review of PR #1431 at 5e35c81547c572e87a741836e636b5d862a1082d found that importing `src/compiler/70.backend/backend/native/isel_x86_64.spl` fails to parse in the deployed aarch64 seed. The two affected AVX2 planner arms end with `else: dest_id = dest.id` after an `if` / `elif` chain. The reviewer observed zero executed AVX examples, whereas main executed its existing examples.

Expected: the single-statement assignment after `else:` has the same semantics as an indented else block and permits the imported AVX2 tests to execute.

Minimal reproducer shape: initialize a mutable integer, branch through `if` and `elif`, and assign that integer in an inline `else: value = replacement`. Compare with the equivalent indented assignment block using the same deployed seed.

The scoped PR repair expands both assignments to indented blocks without changing their conditions or values. This records the compact-grammar limitation rather than claiming the parser itself is fixed. A follow-up parser regression must exercise both forms and require nonzero executed examples on the affected aarch64 compiler, then on the self-hosted phase compiler.

Bounded Windows bootstrap-seed diagnostic after the block-form repair: `test/02_integration/compiler/native/x86_avx512_mir_pipeline_spec.spl` reports `declared>=4 executed=4 passed=3 failed=1 skipped=0 dropped=0` and `Results: 4 total, 3 passed, 1 failed`. The remaining broad SIMD case fails with `avx512-copy-move-shape-mismatch`; the grammar repair is not a claim that the suite passes. This diagnostic used the deployed Rust bootstrap seed solely for parser compatibility, not as self-hosted phase verification. Independent aarch64 confirmation remains required.

## 2026-11-06 note: inline `else: print x` is dropped SILENTLY (Windows x86_64 seed)

Same compact-grammar class, worse failure mode. When a one-line `if c: print a`
is immediately followed by a one-line `else: print b`, the seed executes the
`else` branch but emits nothing -- no parse error, no diagnostic, exit 0. Found
because `simple trace ... --format=sdn` wrote 0 bytes to stdout while the table
format (whose output ends in `\n` and therefore took the `if` branch) worked.

Probe (seed `D:/dev/wt/seed/simple.exe` built from `release/1.0.0` tip
`f1390d48254`, run via `simple.exe run probe.spl`):

| form | result |
|------|--------|
| `if o == "never": print "no"` / `else: print o` | nothing printed |
| `if o == "never": print "no"` / `else: print "lit-" + o` | nothing printed |
| `if o == "never": print "no"` / `else: print(o)` | `hello` |
| one-line `if`, block `else:` | `hello` |
| block `if:`, one-line `else: print o` | `hello` |
| `if o != "never": print o` / `else: print "no"` (if taken) | `hello` |

So the trigger is exactly: statement-form `print` in BOTH one-line branches,
and the `else` branch taken. `src/app/traceability/query_main.spl`
(`query_print_v1`) now uses the block form, with a comment pointing here.
Parser fix still open; this note records the reproducer, not a fix.
