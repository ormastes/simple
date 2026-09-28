# Target 5 Stage4 live projection linker diagnosis (2026-09-29)

Status: diagnostic evidence only. No admitted Stage4 compiler or hello-size
result is claimed.

The previous Stage4 `core-c-bootstrap` build compiled 866 source units with
zero source failures, then reported 12 `rt_*` requests without an admitted
archive owner. `nm` locates all 12 references in two generated modules:

| Object | Simple owner | Runtime references |
| --- | --- | --- |
| `mod_831.o` | `std.nogc_sync_mut.sffi.net` | 10 `rt_net_*` plus `rt_tcp_connect` |
| `mod_835.o` | `std.nogc_sync_mut.sffi.system_hosted_extras` | `rt_execute_native` |

Only `std.nogc_sync_mut.io.tcp` directly references the `sffi.net`
functions among the 866 generated modules. No generated module directly
references `system_hosted_extras__execute_native`. Type and module
registration can still keep these sections live, so this observation alone
does not prove they are disposable.

The saved Stage4 object response file was projected with both BFD and lld,
using the same `-r --gc-sections -u main -u spl_main` roots as
`stage4_live_runtime_requests`. Both projections retain `main` and
`spl_main`.

| Projection | Undefined `rt_*` names | The 12 unowned names |
| --- | ---: | --- |
| Prior saved projection | 728 | Present |
| Fresh BFD projection | 728 | Present |
| Fresh lld projection | 293 | Absent |

The lld result is a promising optional-provider closure, but only a final
link and runtime test can establish whether its dead-section decisions
preserve all required behavior. Do not add unimplemented core-C network or
execution stubs or waive the exact owner gate on this evidence.

A pure-Simple bootstrap tool retry with `SIMPLE_LINKER=lld` compiled the same
866 units with no source failures but stopped **before** the live projection:
that older tool's Stage4 SQLite contract rejected
`spl_sqlite_provider_abi_version_v1` as an unexpected definition. Its hash
is `21aecdb2…f5d175`; the corrected builder recorded in the hello diagnostic
had hash `1ad11693…ba2d5189` and is not present in this worktree's build
artifacts. This retry therefore cannot judge the lld Stage4 link.

The next step at that point was to rebuild the current-source pure-Simple bootstrap tool with the corrected
SQLite contract, rerun the exact Stage4 build with `SIMPLE_LINKER=lld`, and
require a working compiler/hello AOT result before matched size, startup,
and RSS comparisons. Keep the full kernel closure and optional-provider
admission gates open.

## Current-source continuation

The current Rust bootstrap seed and `native_all` archive were rebuilt from
this branch (`simple` SHA-256 `de2e444be5d226b277166b8a2d4c2a756ba99111b5420946d7653996cccdcf26`).
The first pure-Simple bootstrap build compiled 1062 units without source
failure but could not link `rt_native_build` from `core-c-bootstrap`. A cached
retry used the supported `simple-core` hosted archive, reused 1060 units,
compiled 2, linked a 41 MB bootstrap tool, and passed `--version`; that tool's
SHA-256 was `9055558d124d71574ef0cb2202ced70829a87b09de99a5ab04eea73f3112ba60`.

Its exact Stage4 + lld retry compiled 866 units without source failure and
advanced past the SQLite contract. The saved lld live projection retains
`main` and many `rt_*` imports. Every requested import was assigned to the
compiler backfill or core-C providers, leaving **zero Rust runtime roots**.
The Rust capsule projection then rejected that empty subset with `Stage4
requested symbol set is empty`. This does not mean the full live request set
was empty.

The Rust capsule builder now emits a deterministic empty archive for this
specific zero-root case. The focused test verifies that the archive has no
members and no defined or undefined symbols (1 passed). The final Stage4
link must still prove that no missing Rust dependency was concealed.

## Final bounded Stage4 retry

After the empty-capsule change, the current-source Rust bootstrap seed was
rebuilt, then it built a pure-Simple bootstrap tool from 1062 source units
with zero failures. The tool reports `simple-bootstrap 1.0.0-rc.1` and has
SHA-256 `b02fb23dc5e3918b797d1bb2d4af0f5aa3f2cbea02afeb2f6f3e26417334a7c6`.
Its Stage4 + lld retry again compiled 866 units with zero source failures.
The exact provider projections passed; the final link then failed on the
single missing helper `text_dot_from_char_code`, referenced by COFF linker
modules. The Stage4 core-C archive **does define** this symbol in
`runtime_native.o`. The live partial-link object has 304 undefined names;
comparison with the core-C and compiler backfill archive definitions finds
exactly one non-`rt_`/`spl_` provider-owned name: `text_dot_from_char_code`.
The live request filter excludes it, so the core-C capsule localizes it and
the final lld link cannot resolve it. The next change should classify this
known legacy runtime helper in the exact live request set and prove the
capsule keeps exactly that owner. No further build was run after this third
focused Stage4 verify/fix cycle. There is still no admitted Stage4 executable
or hello size/startup/RSS cohort.
