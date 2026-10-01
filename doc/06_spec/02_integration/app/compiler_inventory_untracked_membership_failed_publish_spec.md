# Compiler inventory failed membership publication spec

Executable source:
`test/02_integration/app/compiler_inventory_untracked_membership_failed_publish_spec.spl`.

The spec admits a cold Git inventory with one untracked source, adds a second
untracked source, and writes a framed SCV `overflow` journal event. It checks
that refresh rejects the event, leaves the admitted inventory pointer and
old immutable membership record intact, and removes the candidate record.
After removing the journal, it checks that warm refresh admits all three
sources, publishes the new record, and retires the old one.

The 2026-09-28 no-stub native execution reported one example and zero
failures. See
`doc/09_report/compiler/target6_membership_failed_publication_2026-09-28.md`
for binary identity and remaining qualification work.
