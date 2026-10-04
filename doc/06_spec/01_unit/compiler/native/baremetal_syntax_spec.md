# Baremetal syntax specification

> Hand-authored mirror of [the executable SSpec](../../../../../test/01_unit/compiler/native/baremetal_syntax_spec.spl). The previous generated manual described literal-only assertions as parser coverage. This manual records the new AST oracles without claiming a generated or passing run.

## Purpose and execution

Compiler engineers use this spec to check the self-hosted frontend's handling of baremetal syntax. Each snippet is passed to `core_frontend_parse_reset` or `parse_and_build_module`; assertions inspect the resulting declaration, expression, or module AST. The spec has no `main` function, so its `describe`/`it` blocks are the executable entry points. A compiled SSpec run is required to establish a verdict; interpreter loading alone is insufficient.

**Execution status:** UNRUN on this source revision. No bootstrap, native fixture, or SPipe docgen result is claimed. Known source inspection predicts failures in the volatile, C representation, fixed-address, and static-assert fact checks; treat them as real feature gaps until a compiled run and compiler repair prove otherwise.

**Source SHA-256:** `305921f504a7e35cf3dac288c4b571c552bb9d477f4086e14b119896000f04da`.

## Scenarios and evidence

| Group | Scenario | Executable oracle |
| --- | --- | --- |
| Volatile | Parsed register field | `ParserStruct.fields[0].is_volatile == true` |
| Volatile | Module variable | `ParserConst.is_volatile == true` |
| Unsafe | Keyword | Flat expression arena contains `EXPR_UNSAFE_BLOCK` |
| Unsafe | Block body | Unsafe expression retains one parsed statement |
| Interrupt | Bare handler | Declaration placement equals `interrupt` |
| Interrupt | Vector argument | Declaration placement equals `interrupt(32)` |
| Interrupt | Nil match control | The executed nil arm returns `-1` |
| Layout | `@repr(C)` | Parsed struct attributes resolve to `TypeLayoutKind.C` |
| Layout | `@packed` | Flat declaration is packed and has field widths `[1, 31]` |
| Layout | `@align(16)` | Function placement equals `align(16)` |
| Layout | Bitwise control | Five operators return fixed arithmetic results |
| Bitfield | Declaration | Parsed module has the `ControlReg` bitfield |
| Bitfield | Field widths | Flat declaration retains widths `[-1, 1, 3]` |
| Address | Fixed register address | Parsed constant retains `0x40000000` as fixed address |
| Static assert | Compile-time assertion | Parsed module contains one static assertion node |
| Const function | `const fn` | Parsed declaration is marked compile-time callable |

The source snippets themselves are the test inputs. Every `parse_and_build_module` scenario first requires zero parser diagnostics, then checks its AST fact. The `core_frontend_parse_reset` scenarios require a successful parse before their AST checks. An assertion on a string literal is never used as evidence of parser support. Missing AST data causes the relevant scenario to fail. The nil match and bitwise scenarios remain direct execution controls and make no parser claim.

## Verification and recovery

Run the compiled SSpec with the admitted self-hosted runtime and the complete compiler/lib source inventory under the release verification harness. Record the exact source and compiler commits, backend, mode, case count, failures, and output log before changing this status. A failure in one of the four known gap groups calls for a parser/flat-bridge feature repair or an explicit unsupported-feature decision; changing expected values to string checks would restore the original false coverage. After a source edit, regenerate this manual with `simple spipe-docgen` when that tool is admitted and compare the generated scenarios with this table.

## Limitations

These are frontend and small execution oracles. They do not establish hardware MMIO behavior, interrupt ABI correctness, layout byte offsets, or compile-time evaluation of the assertion. Those require separate backend/runtime tests. The legacy mirror under `test/unit/` is outside this canonical source path and remains a separate migration item.
