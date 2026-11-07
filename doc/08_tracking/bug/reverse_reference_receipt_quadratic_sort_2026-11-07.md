# Reverse-reference receipt sorting stalls full CLI compilation

Status: source repair authored; native correctness and performance qualification NOT_RUN.

## Actual evidence
Other-session a92 producer a92bc18646b859ee6b034ff7a97de2e9175d30accb787e18373bd7e436c73459, source d21afc1bf024c08f476b744f8a8c2a606c501205, LLVM/Darwin. One1second10ms sample of PID7431 contained76/77mainthread stacks in reverse_reference_sorted_v1. Retained CURRENT receipt contained73779rows and37075600bytes. FullCLI completed16/3086modules at6325785ms; individual staged codegen intervals2478759ms and1293892ms. Point-in-time sampling does not attribute the whole build or establish a candidate speedup. Raw evidence lives in campaign runtime-audit/a92-fullcli-stack-sample.txt and a92-reverse-receipt-bottleneck.md. Other-session source/process/caches were not altered.

## Cause and repair
Insertion sorting is quadratic in rows. Publication encoded/sorted the same receipt again to derive its digest. Normal NUL-free projection rows now use the existing common canonical identity heapsort (O(nlogn) comparisons, existing array semantics); publication computes digest from its alreadyencoded content. Wire framing, schema, duplicate multiplicity, pointer naming, public exports and invalid receipt behavior are unchanged. No cache format bump or invalidation workaround.

Comparator proof scope: core-C rt_text_cmp_any uses strcmp; hosted rt_text_cmp_any compares lengthdelimited unsignedbytes. Both agree with canonical_identity_text_lt for NUL-free validUTF8 includingprefixes. Core-C stops at embeddedNUL, which historicalreceiptvalidation permits. Any encodedrow containingNUL therefore takes the unchanged stable insertion path; its O(n²) behavior remains explicitly open. Identical-row stability under heapsort does not change serializedbytes. No crossproviderNUL semantics are normalized.

## Qualification
New exact-byte unit tests compare old insertion ordering against production receipt output for Unicode/prefix/duplicates/NUL, emptyandinvalidconsumers and actual filesystem publication/taggedhash. Existing digesttag and projectionv2 suites remain adjacent obligations. Performance fixture uses73779productionrows with duplicatepayloads and verifies cardinality/order/taggeddigest. It is representative cardinality, not identical capturedproductionbytes. No productionhelper is copied into a runtime harness; the oldsort in unit test is only an independent compatibilityoracle.

Required pending measurements: immutable baseline/candidate binaries on samehost, samefixtures at4096/8192/73779rows, p50/p95elapsed plus peak/steadyRSS, outputhashes and provideridentities. No measuredimprovementclaim until collected. OptimizeCLI and realSSpec runner are unavailable; no seedfallback. Sourcealgorithm bound and authoredtests are not runtimePASS.

A correctedsource does not accelerate an alreadyrunning bakedproducer. Future cache-preserving continuation requires an admitted correctedproducer, unchanged cacheauthorityrules and real resourceadmission; never remove receipts or weaken reserve to hide this hotspot.

## Bounded production-import diagnostic proposal
Fixture test/fixtures/compiler/cache/reverse_reference_sort_production_probe.spl imports actual key/receipt/digest owners, verifies a fixed byte frame with duplicated rows and exact digest, returns distinct11–13 failures. No copied encoder or fake test engine. This checks only three-row byte/digest behavior, not publication/NUL/performance. Receiptowner imports IO/phasecompatibility, so actualclosure may exceed expectedtinyfixture; obtain canonicalclosure/resource admission first. Proposed distinct newcause budget: one compile under180second/2GiB watchdog with preserveda90 authority, isolatedsource/cache/output and exactmanagedsemanticenv; no execution authorized by this document. DarwinSMF limitation stillapplies: use native-build only when reserveadmitted, or independentlyreviewed completeIR/object/initlist downstream. Do not consume exhausted i32/provenance attempts or assume a killedcompile is successful.
