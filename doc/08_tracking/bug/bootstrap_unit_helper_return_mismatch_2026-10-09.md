# Bootstrap Unit helper return mismatch

Status: fix prepared; updated-producer native verification pending.

The admitted Linux Stage 2 compiler SHA256
`2f34befeaca05b0cd4e389f4cda2e0d1558e15a8342f9b60f7fbacfa528830ae`
rejects an unannotated, side-effect-only helper with `E-SFFI-016: missing return
in non-unit function`. The LSP MCP closure independently reproduces this for
`print_usage`, `lsp_serve_stdio`, `write_stdout_message`, `exit`, `report_error`,
location setters and virtual-source consumer installation/clearing.

Minimal real native reproduction: compile
`test/fixtures/native/bootstrap_unit_helper/main.spl` with
`SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1`, Cranelift, entry closure,
`core-c-bootstrap`, and the runtime capsule bound to the producer above.
The baseline fails at MIR for `print_usage`, line 1:1; no executable was
produced. Diagnostic log: `/tmp/lsp-unit-probe-baseline-cold.log`.

Owner: `20.hir/hir_lowering/_Items/declaration_lowering.spl`.
For an unannotated helper, bootstrap lowering selected the builtin fallback
`i64` while `lower_hir_block_unit` deliberately supplied no trailing operand.
The existing return scanner now limits that fallback to bodies containing an
explicit value return. Side-effect-only and bare-return helpers retain Unit;
existing explicit value-return bootstrap ABI and main handling remain intact.

Regression: `test/unit/compiler/hir/untyped_return_nil_safe_spec.spl` checks
three Unit cases and retention of an explicit integer return. Run the native
fixture with the regenerated producer, assert stdout `unit-helper\n` and exit
zero, then retry the LSP closure. The independent unresolved `unwrap` failure
is not resolved by this change. No release qualification is claimed here.
