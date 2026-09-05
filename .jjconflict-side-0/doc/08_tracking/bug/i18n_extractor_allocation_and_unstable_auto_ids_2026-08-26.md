# i18n extractor allocation density and unstable auto IDs

The current extractor allocates 20,495 times and 2,879,182 bytes for 4,096
explicit messages: about five allocations and 703 bytes allocated per message.
The live result is 1,626,128 bytes and transient peak is 2,206,445 bytes above
the already-parsed fixture.

It also promotes heuristic alphabetic plain strings into persistent entries and
generates IDs from mutable scope counters. Unrelated insertion or traversal
changes can therefore churn catalog identity.

Required redesign: explicit localized constructs are authoritative; heuristic
discovery is an opt-in audit. Persist stable package/module/key IDs, retain
borrowed spans or interned text through extraction, and compile once into the
typed catalog schema/IR. The optimized hot extractor must report reduced
allocations and stable IDs under unrelated source edits.
