# ISO move pipeline fixture function attributes

The primitive iso and non-iso HIR fixtures constructed `HirFunction` with
`func_attr: nil`. The canonical HIR field is nonoptional `FunctionAttr`;
declaration lowering initializes it with `FunctionAttr.default()`. MIR lowering
and provider metadata read its fields, including `is_global`. All three
primitive cases therefore failed before their real MIR/NLL assertions with
undefined field `is_global` on nil. The existing struct fixture already used
the correct default and passed.

Repair the two invalid constructor sites with `FunctionAttr.default()` and
import `BorrowChecker` from its defining module explicitly. No production
owner, symbol table, case intent, assertion, or NLL implementation changes.
The non-iso case necessarily changes its fixture constructor in its body;
its instructions and assertions remain unchanged.

Baseline: build/phase1-borrow-owner-imports-20261011/
iso_move_pipeline_spec-c7badcd951491e1a-residual.json records four executed,
one PASS and three FAIL. After repair, only the three previous failures were
collected once: three executed, three PASS, zero FAIL. The existing struct
PASS was not replayed. This is incremental four-identity coverage, not a
full-file rerun.

Receipt: build/phase1-iso-fixture-20261011/evidence.json pins the release base,
fixture and entry hashes, terminal log hash, exact case identities, producer
and retained invocation environment. Producer SHA256:
15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb.
Imports use the retained Phase1 SIMPLE_LIB source snapshot. Qualification is
BOOTSTRAP_DIAGNOSTIC_ONLY, with current imported owner admission false.
No compiler rebuild, seed source change, pure-runtime/native admission, or
closure of the separately documented iso/mut parser gap is claimed.
