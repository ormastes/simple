# Primary Linux-tool launch matrix v1

Status: implemented as a bounded, non-authorizing catalog plan; runtime unverified.

The closed matrix contains twelve commands backed by existing pure-Simple entry
owners. Eight (`echo`, `true`, `false`, `pwd`, `seq`, `cat`, `head`, `wc`) are
authenticated aliases of the single `/bin/simplebox` payload. Four
(`sha256sum`, `md5sum`, `grep`, `ps`) are separate payload identities. The boot
bundle therefore contains exactly five signed records, never twelve duplicated
payload records.

Every row records its command path, canonical payload path, source entry owner,
and least textual capability intent. These strings are inventory data, not
kernel capability tokens. The catalog plan accepts records in any input order,
normalizes them to canonical order, rejects missing/extra payloads, rejects
aliases on standalone payloads, and freezes the exact Simplebox alias vector.
The package-private consumer revalidates the plan and delegates Ed25519 trust
verification plus catalog mutation to the existing boot owner.

Mapping readiness comes only from
`executable_target_process_image_ready_v1`. Consequently x86-64, AArch64, and
RV64 rows are mapping-ready in current policy, while x86-32, ARM32, and RV32
remain false. This is not execution evidence: target bytes, signed manifests,
filesystem admission, live loader authority, and QEMU receipts remain required.

The matrix construction is O(12), and bundle validation is O(5 squared) through
the bounded shared boot-policy uniqueness checks. It allocates only the fixed
12-row matrix or fixed five-record ordered bundle and never copies payload bytes.
