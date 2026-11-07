# Shared classifier diagnostic attempt 1

The single authorized attempt stopped before compilation with `SCV-E-ADMISSION: directory-alias-inventory-invalid`. Canonical receipt: status complete, exit 1, quiescent 1, peak RSS 101492 KiB within enforced 4194304 KiB. The fixture did not execute; zero assertions are runtime-proven. No retry was attempted or authorized.

Evidence: `build/hir-export-helper-attempt1/{build-command.txt,authority.sdn,build.log,build.env,result.sdn,source-manifest.sdn,source-identity.sdn,postflight.sdn}`. Source snapshot commit bc4e9e30812090557ed71b8ff8a2d6e21782b715 retained unchanged after admission failure. This is an admission blocker, not evidence of classifier correctness or failure.

Source/design review by Astra passed after direct bootstrap lower_module export lifting and actual assertion-count enforcement were added. Actual HIR lowering specs, generated-manual validation, compiler/lib/MCP/LSP checks and bootstrap integration remain unexecuted. Bug claim is wait-verify (fix-implemented-verification-pending), not fixed.

Compact immutable receipt copies are committed beside this report as `attempt1-*`; the full source manifest and snapshot remain local at the evidence path above. Build log SHA256 d6984f1220df536cbd0ce49c04c5eeada306d0246790c293e0c8df3fa24d700e; receipt SHA256 9659af77eacb74b150d75a9c10cf531971bb9756cd3252964a257ee4ea76c40c.

Root-cause follow-up: our archive omitted the tracked targets of src/app/{cmm_lsp,mcp_t32,t32_cli}. All three aliases were dangling because examples/10_tooling/trace32_tools/{cmm_lsp,t32_mcp,t32_cli} were absent. Retained bf388 inventory_aliases and dir_ops match its recorded source; this is a defective input snapshot, not an established producer bug. Attempt1 remains failed. Root explicitly authorized one separately recorded corrected-input attempt2, with no further retry.
