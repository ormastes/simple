# Scenario artifact component bounds

Stage: owner tests red/green; review pending.

Rust scenario artifact naming now bounds long ASCII slugs to 180 bytes and
uses a full SHA-256 suffix over original framed fields. Short paths and full
manifest names remain unchanged. Actual directory creation reproduces the old
failure and passes after the fix. Isolated native owner harness: 5/3 before,
8/0 after. Full driver and native Simple runner were not rebuilt for this change.

The three arena failures require missing byte-storage APIs and a quota constant;
the V2 module is absent. These failures and output-parser group attribution are
separate open issues. No arena assertion, feature semantics or success count is
changed by this fix.
