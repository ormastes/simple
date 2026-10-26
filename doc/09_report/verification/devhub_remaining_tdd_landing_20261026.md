# DevHub remaining TDD fixes

Targets release/1.0.0. Ordinary application imports select std.* providers through configuration. Provider owners retain explicit physical imports where required.

Includes UTF-8 OAuth form encoding through the shared URL encoder; typed SDN, MinIO and SQLite result bindings; native-static flag tables; Windows temporary-directory fallback; missing TCP/process facade exports; SSpec facade and typed hook storage fixes; MIR integer tuple metadata and nested lifted-definition publication. Adds real process, compiler and native cipher/SSpec regression fixtures.

## Evidence and limits

Previously qualified and merged separately: native clock, SDN child tuples, AES UTF-8 credentials, DEFLATE NLEN, PBKDF2-SHA512 (PR4864), mail bridge (PR4791), SigV4 (PR4852). These changes are not duplicated here.

The local phase-2 producer compiled the Messenger graph after explicit SQLite tuple bindings; unsigned SQLite varint and encrypted fixture hash checks passed. The production Messenger history read still panicked before returning. The final boundary build was still in progress at packaging; it is not passing evidence.

The full real SSpec nested-callback probe failed to link on the existing phase-2 producer. The named callback control failed MIR resolution for chained to_equal. No full SSpec suite, four-family runtime matrix, Messenger decryption/tamper pass, or phase-3 qualification is claimed. Compiler source fixes require a rebuilt producer before their behavioral regressions can run green. Added system tests require a source-matched DEVHUB_SYSTEM_BIN and fail when unavailable.

The unsuccessful public expect return-type experiment was reverted. Upstream native wrapper implementation supersedes the old local preprocessing experiment; that experiment is excluded. Foreign window-manager goldens are excluded and preserved in the original worktree. Repository six-cycle limits prevent further iterative retries for these features.
