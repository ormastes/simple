# Phase 1 ISO parser probe reaches MIR lowering

The retained `iso_parse_pipeline_spec.spl` run stopped after 40 seconds without
a terminal verdict. That receipt remains unresolved; a timeout alone did not
identify a parser defect.

Release source observation: `a4ca8226e21f8df3374c3eea1109e6365c4d7d79`.
The cached bootstrap producer SHA256 is
`15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`.
It is unadmitted. Imported compiler owners still come from the retained
`phase1-real-spec-pilot40/source/src` tree through `SIMPLE_LIB`; the isolated
working directory does not prove that current release owners were executed.

## Bounded evidence

Evidence directory: `build/phase1-iso-parser-diagnostic-20261011/`.

1. Previous original consumer run: 40-second timeout, no terminal counts.
2. `receipt.json`: the first original case, with stage markers, exits 1 after
   25.922 seconds. Parse, HIR lowering and target-context construction complete.
   The next marker precedes `lowering.lower_module(hir)`, which fails with
   `semantic: type mismatch: cannot convert enum to int`.
   Entry SHA256: `fa8ba1f66e2dc8611d2edf5d4b3c8881007c917da6267a0d8e950ce7bb2d7638`.
   Log SHA256: `01e983f8211ee8149a743252c743eda92337763f40aa53bdd78e6aa87c7fe73d`.
3. `function-receipt.json`: a distinct diagnostic calls `lower_function` on the
   single parsed function, bypassing module registration. It exits 1 after
   30.741 seconds with the same conversion error, before the completion marker.
   Entry SHA256: `de17fc7685549a7e530fee0eafbb21867b3570cbb95d8ccbb47a02267b20e0f3`.
   Log SHA256: `36f29e92f29bcff7b7feb91949c5fc6fad6e5eb464c15b3a137a98394ee337d1`.

These diagnostics localize the observed failure to the cached function-lowering
path. They do not identify the offending conversion or establish a current
release implementation defect. The direct-function diagnostic is not the
original three-case pipeline spec. No original assertion was weakened and no
queue row was closed.

## Remaining work

Obtain a source-resolved current-owner interpreter or native receipt, identify
the conversion, and then verify the original three cases without dropping any
pipeline stage. ISO-local transfer metadata is investigated in a separate
owner lane; its repair must not be inferred from these parser diagnostics.

The three-attempt boundary is reached. No fourth attempt, compiler rebuild,
passing-test replay or cache deletion was made. STATUS: WARN; original parser
pipeline acceptance and production runtime qualification remain open.
