# Declared local ISO transfer metadata

Executable: test/01_unit/compiler/borrow/iso_declared_local_state_spec.spl.
Requirement: REQ-ISO-DECLARED-LOCAL-TRANSFER.

The first case constructs real HIR statements and calls the production MIR
statement owner. A fresh integer with an explicit isolated declaration must
have scalar isolation state one; rebinding it must emit exactly one matching
Move instruction and retain isolated destination metadata. The second case
requires exactly one matching Copy for ordinary integer bindings. Both require
zero MIR lowering errors. No parser, MIR instruction, or NLL result is mocked.

Current qualification is BLOCKED: two new cases executed, zero passed, two
failed with enum-to-integer conversion before their assertions. A separate
one-case stage diagnostic places that error inside the lower_stmt call after
the real lowering/builder constructors complete. It is not an acceptance PASS.

Evidence: build/phase1-iso-e2e-20261011/ and
doc/08_tracking/bug/iso_local_declaration_metadata_loss_20261011.md.
Cached bootstrap-only diagnostics request the isolated current source root;
actual complete owner resolution, admitted self-hosted behavior, native paths,
and the original end-to-end use-after-move assertions remain unqualified.
