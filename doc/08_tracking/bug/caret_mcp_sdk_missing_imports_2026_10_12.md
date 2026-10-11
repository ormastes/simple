# Caret MCP SDK missing protocol imports

Source 523ce4c9b47f81f1472f121bcac84a4238fb5c76; P2 producer SHA256892b220e19b5cbafd620190c95b9a2f26fc5ebc08304b8b07d4475da0ea7abb0.

General LLM Caret main originally failed HIR in two modules: core/jsonrpc.spl34 calls jo4 without importing it; helpers_compat.spl612/613 call print_raw without importing an owned printing facade. Focused original module attempts failed in8.66s and16.12s and the exact errors are retained in p2-caret-essential/focused-hir-failures.json. These missing imports also exist on remote release_phase3 8390be74.

The candidate imports existing jo4 and SOSIXstdio.sosix_print_raw respectively. No deleted tools or stub provider. Changed jsonrpc native module succeeds: exit0,30.477s,94520bytes. Changed helper HIR succeeds51/51 but its object build times out120s at MIRstart; no helper object or full Caret qualification is claimed.

The executable native fixture test/fixtures/bootstrap/caret_jsonrpc_import_owner_probe.spl checks the real builder's exact four-field JSON request and emits it via the owned SOSIX alias. Its compilation/runtime status is recorded independently after executing the fixture.

Actual Caret Suite entry is app/llm_caret/cs_main.spl, distinct from general LLMCLI main.spl. Its first native attempt fails HIR165/169 due imported SimpleRing<Op,Cpl> parameters leaking as unresolved types into four SOSIX modules. That generic-class specialization bug is separate and remains open. No suite binary or full SPipe PASS is claimed.

Fixture diagnostic notes: actual jsonrpc_request return decoded by GDB exactly matches four-field JSON. An ordinary expected literal lost its last closing brace because `}}` escapes one brace. The attempted raw-single-quoted expectation then failed P2 parsing with expected colon/got StringLit at8:20. Final fixture uses explicit doubled opening/closing braces. The raw-single-quote grammar gap remains recorded; no fabricated protocol/library failure is claimed.

Final native request fixture PASS: compile exit0 in42.996s, object101056B; strict fresh C/Rust manual link exit0, ELF2887352B; execution exit0,stderr0,stdout53B independently parsed as exactly jsonrpc2.0,id7,methodecho,params emptyobject. Artifact: /mnt/c/Temp/simple-manual-lanes-20261011/p2-caret-jsonrpc-native-probe-braces/link-run-receipt.json. This qualifies the request-builder/import regression, not the whole Caret Suite or helper-native object.
