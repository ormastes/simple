# Preserve artifacts for long scenario names

Authored manual for focused Rust owner tests, not generated SSpec evidence.

1. Give a scenario a long ledger-style group name. Create its planned directory
   on the actual filesystem and write/read the manifest there. Require a bounded
   directory component and the complete original group and scenario text.
2. Give two scenarios the same long prefix but different suffixes. Require
   distinct deterministic names. Move text across the group/name boundary and
   require that those distinct fields also produce distinct digests.
3. Use long names that differ only in Unicode characters removed by slugging.
   Require distinct ASCII directory names. Existing short paths stay unchanged.

The isolated native owner-module harness reproduced the filesystem error before
the fix (five passed, three failed) and passed all eight tests afterward. This
does not represent a full driver build or a native Simple arena-suite pass.
