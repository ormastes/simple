# Class owner identity fixture

Entry: src/identity/main.spl. Source root: src within this fixture directory.
The nested src root gives declarations and imports the same identity when the
fixture is built from different checkout paths.

With an admitted self-hosted runtime, build an entry closure for that entry,
then run it. Expected exit: 0. The program asserts checksum 103034443, nested
Leaf values 7/17, constructor overrides 41/51, helper-main value 404, local and
imported function-pointer values, and array push value 73.

Inspect definitions and references too: the two providers' Cell methods,
default_value helpers, and identity.left.main must remain distinct. The actual
entry main, extern declaration, exported checksum function, and @global guard
retain their ABI names. This fixture has not yet been executed in the P3 lane;
see doc/09_report/class_owner_identity_2026-09-22.md for the runtime blocker.
