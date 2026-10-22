# Windows T32 physical import candidate

Status: source candidate; executable verification UNRUN; not landed or deployed.

The full-CLI diagnostic closure selected 2,672 source modules but omitted the
physical T32 application under `examples/10_tooling/trace32_tools/t32_cli`.
HIR then failed to resolve `t32_cli_main` from `app.t32_cli.mod` in
`src/app/cli/_CliMain/main_and_help.spl`. Git records `src/app/t32_cli` as a
symlink; this Windows checkout materializes its 47-byte target as a plain file.

The candidate adds a qualified driver fallback for `app.t32_cli` and a native
entry-closure fallback under an explicitly selected `10_tooling` source root.
Existing direct source roots retain precedence. The closure fallback stays
inside its supplied source root, including SCV snapshot paths. It adds no
filesystem probes for unrelated imports and no new directory-scan implementation.
Successful physical fixed probes avoid the existing numbered-directory fallback;
missing physical paths may still enter that fallback through the existing helper.

Three driver regression cases cover the module alias, a trailing function
import, and the prefix boundary. They accept a working checkout symlink as well
as the physical fallback. These cases are not executed yet. Native closure
membership, explicit root precedence, and frozen snapshot identity still need
behavioral verification with a compiler containing the change. No successful
build is inferred from static source inspection. Authoritative bug DB/tag
reconciliation remains owned by the other sessions as requested.
