# Target 6 membership publication rollback (2026-09-28)

**Focused correctness result: PASS.** A warm inventory refresh that sees a new
untracked path now removes its newly written immutable membership record if
filesystem event application rejects the batch. The previously admitted
`source-inventory/CURRENT` pointer and its membership record remain intact.

The refresh validates the SCV journal before writing the new record. It must
still write that record before publishing a pointer that names it. If event
application fails, the refresh checks that the pointer is unchanged and that
the record is readable, then deletes only a record created by this refresh.
The refresh lock protects this check against other production publishers.
If ownership or deletion cannot be established, refresh fails closed and
retains the record.

`test/02_integration/app/compiler_inventory_untracked_membership_failed_publish_spec.spl`
starts with an admitted Git inventory, adds a second untracked source, and
injects a framed SCV `overflow` event. It checks rejection, pointer stability,
retention of the old record, absence of the candidate record, and successful
retry after removing the journal. The no-stub Stage2 entry-closure native
binary reports **1 example, 0 failures**; SHA-256:
`071236eab53a6c02b66c9a2fa53a63752d84ea7646dafd43c3f632d626e6b5e1`.
The existing successful-retirement integration spec also reports **1 example,
0 failures**; binary SHA-256:
`5a04fa44396a82051dbf789d411f14af4e348de51925f0908154be2f65639d73`.
Both used the admitted pure-Simple Stage2 compiler SHA-256
`d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`.

This is a focused publication and rollback check. It does not qualify the
full Target 6 event route, concurrent writer behavior, realistic native
performance, or the persistent typed graph publisher.
