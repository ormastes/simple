# i18n locale generation allocation density

Generating 4,096 multilingual declarations currently performs 20,495 heap
allocations (about 5.00/message), retains 385,024 bytes for 352,350 output
bytes, and reaches 577,767 transient bytes above the prebuilt fixture. See the
matched receipt in `doc/10_metrics/text_i18n/`.

Replace per-entry `format!` construction with a capacity-planned `TextBuilder`
or byte sink that appends headers, identifiers, delimiters, and escaped valid
UTF-8 runs directly. Acceptance requires matched output, zero per-entry
temporary allocations, allocation/byte counters, p50/p95/p99, peak RSS, and
zero retained bytes after output disposal.

