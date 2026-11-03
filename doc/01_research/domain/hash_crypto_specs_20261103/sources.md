# Pinned official specification sources

Status: SOURCE_ACQUIRED / REQUIREMENTS_DRAFT. No execution or branch-coverage claim.
Acquired 2026-11-03 UTC. Original bytes are in private cache
`C:/dev/p3new/hash-coverage-20261103/spec-cache`. This directory is not a portable
repository dependency; retrieve the URLs below and verify SHA-256 on another host.
Downloads used unique temporary files and no-overwrite moves. No official XXH3
PDF was identified. gxHash's upstream README links an author paper, downloaded
as `gxhash-article.pdf`: revision 1, November 2023 (21 pages), historical design
context rather than an automatic current-HEAD conformance oracle.
RFC Editor PDF endpoints `/rfc/pdfrfc/rfc{8439,7748,8446}.txt.pdf` returned HTTP 404;
the canonical RFC Editor TXT originals were downloaded instead. No locally printed
PDF is represented as an official publication.

Git revisions: BLAKE3-specs `ac784c9f22a48327782f042ec2f4d8126b3b1744`;
xxHash v0.8.3 `e626a72bc2321cd320e953a0ccf1584cad60f363` (spec text version 0.2.0,
2023-06-29); gxHash HEAD `5e00a497289d1c2f0ae07e5f956654c77f1cfc09`.
Current upstream gxHash is NOT automatically the revision implemented by Simple.

BLAKE3 published vector corpus is separately pinned to the implementation repo
`BLAKE3-team/BLAKE3` commit `f55849f89cd85083c1c9daa2c5de20766f309c00`;
`blake3-test-vectors.json` is original upstream JSON interoperability data.
The downloaded Apache-2.0 license accompanies that implementation source.
The gxHash article is summarized only; repository MIT licensing is not taken as
independent confirmation of every figure/third-party paper right.

PDF local extraction: pypdf, per-page text into `*.extracted.md`: BLAKE3 31 pages,
FIPS 197-upd1 46 pages, SP 800-38D 39 pages, FIPS 186-5 86 pages, gxHash 21 pages. Extraction
completed, with missing fontTools/CFF encoding warnings for some glyphs. Treat
equations, ligatures and code as unverified transcription; check original PDF
visually before copying an oracle. Private extracted text is analysis material;
the checked-in notes are original structured summaries, not complete transcriptions.

| Cached original | SHA-256 | Official URL | Retrieved UTC |
|---|---|---|---|
| `blake3.pdf` | `ce179e62f29a6e43ec1ac2fe62b5e063a18632cf936c430d1373bfa0b81fb349` | [blake3.pdf](https://raw.githubusercontent.com/BLAKE3-team/BLAKE3-specs/ac784c9f22a48327782f042ec2f4d8126b3b1744/blake3.pdf) | 2026-11-03T02:01:01.1063989Z |
| `blake3-license.txt` | `0263d0385e90f675644dcf1aaf979a5559855f86a6b41d005c53ae27c9a9bb76` | [blake3-license.txt](https://raw.githubusercontent.com/BLAKE3-team/BLAKE3-specs/ac784c9f22a48327782f042ec2f4d8126b3b1744/LICENSE) | 2026-11-03T02:01:01.4203323Z |
| `xxhash_spec.md` | `61c47af338b2feefcc7621700ef6b941bcf9b1dd33899c503f68cb797e7ef333` | [xxhash_spec.md](https://raw.githubusercontent.com/Cyan4973/xxHash/e626a72bc2321cd320e953a0ccf1584cad60f363/doc/xxhash_spec.md) | 2026-11-03T02:01:01.7245612Z |
| `xxhash-license.txt` | `6ffedbc0f7878612d2b23589f1ff2ab15633e1df7963a5d9fc750ec5500c7e7a` | [xxhash-license.txt](https://raw.githubusercontent.com/Cyan4973/xxHash/e626a72bc2321cd320e953a0ccf1584cad60f363/LICENSE) | 2026-11-03T02:01:02.0278732Z |
| `gxhash-readme.md` | `71e86a2ffde8cc3e9736fa3f5c9b609e21670d50f8720a712e03e04b72ddd3d7` | [gxhash-readme.md](https://raw.githubusercontent.com/ogxd/gxhash/5e00a497289d1c2f0ae07e5f956654c77f1cfc09/README.md) | 2026-11-03T02:01:02.2968335Z |
| `gxhash-lib.rs` | `e026efe4250bc984f8257317d349ba651fb86c5b7d06efec8bf9e223b8190a4d` | [gxhash-lib.rs](https://raw.githubusercontent.com/ogxd/gxhash/5e00a497289d1c2f0ae07e5f956654c77f1cfc09/src/lib.rs) | 2026-11-03T02:01:02.5758467Z |
| `gxhash-license.txt` | `1775b5819b22ff8b57fae313035b6256e87a0d1ee15c461259ec371278940728` | [gxhash-license.txt](https://raw.githubusercontent.com/ogxd/gxhash/5e00a497289d1c2f0ae07e5f956654c77f1cfc09/LICENSE) | 2026-11-03T02:01:02.8963275Z |
| `fips197-upd1.pdf` | `62c86eb567f13edb8f71826e985da870b04ef6381634f303cdb16e84d47becd1` | [fips197-upd1.pdf](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf) | 2026-11-03T02:01:04.2945124Z |
| `sp800-38d.pdf` | `d99f3921ccebca049e7522426553aba071dae14ec3d5b6041e8c111a6cb57bba` | [sp800-38d.pdf](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf) | 2026-11-03T02:01:05.4599492Z |
| `fips186-5.pdf` | `fbb9c7c2ba442f03c57b63b43c888311903c9d0f29f89b06efdebd9b619140c5` | [fips186-5.pdf](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.186-5.pdf) | 2026-11-03T02:01:07.5317603Z |
| `rfc8439.txt` | `25bef70fbf7a07ff45c2fe4cb7c6ce954eac687413d8610603268b4e4415324c` | [rfc8439.txt](https://www.rfc-editor.org/rfc/rfc8439.txt) | 2026-11-03T02:01:42.2215655Z |
| `rfc7748.txt` | `279ca0ecc5e92e2962e27b846986aeb74729d9dd34bd4a04a362f80dcb596ad3` | [rfc7748.txt](https://www.rfc-editor.org/rfc/rfc7748.txt) | 2026-11-03T02:01:42.5664154Z |
| `rfc8446.txt` | `47871bc8820a2c3b6ea89f061055577058862cf543686b82d10131239702b3bd` | [rfc8446.txt](https://www.rfc-editor.org/rfc/rfc8446.txt) | 2026-11-03T02:01:42.8885994Z |
| `gxhash-mod.rs` | `37b72c759c3772369017a8a1b7ea552e6ee1bc4c2e950c69792b125b4b21505e` | [gxhash-mod.rs](https://raw.githubusercontent.com/ogxd/gxhash/5e00a497289d1c2f0ae07e5f956654c77f1cfc09/src/gxhash/mod.rs) | 2026-11-03T02:02:30.6735494Z |
| `xxhash.h` | `17973c0dc49d9854ca26caa191f0e12f7a424b68858d9a78de3860d959d85e4b` | [xxhash.h](https://raw.githubusercontent.com/Cyan4973/xxHash/e626a72bc2321cd320e953a0ccf1584cad60f363/xxhash.h) | 2026-11-03T02:03:59.5431266Z |
| `blake3-test-vectors.json` | `dcb91ea8accc77e6d6e632af7cdc1a99a9f3ae78cf648da595c7d064db32f624` | [blake3-test-vectors.json](https://raw.githubusercontent.com/BLAKE3-team/BLAKE3/f55849f89cd85083c1c9daa2c5de20766f309c00/test_vectors/test_vectors.json) | 2026-11-03T02:06:24.5353223Z |
| `blake3-code-license.txt` | `00fcc7a934ddbc9ece2a7cc063ac788e284b703b1d705ccbba72d462aa97921e` | [blake3-code-license.txt](https://raw.githubusercontent.com/BLAKE3-team/BLAKE3/f55849f89cd85083c1c9daa2c5de20766f309c00/LICENSE_A2) | 2026-11-03T02:06:24.8868245Z |
| `gxhash-article.pdf` | `cfd0502072786e4219e7ff18579c6e8e26ccbb60d3e8f92f51d9ab1b2062553e` | [gxhash-article.pdf](https://raw.githubusercontent.com/ogxd/gxhash/5e00a497289d1c2f0ae07e5f956654c77f1cfc09/article/article.pdf) | 2026-11-03T02:07:06.9768612Z |

## Rights and revision caveats

- blake3: CC0-1.0 OR Apache-2.0; preserved upstream LICENSE
- xxhash: Specification has its own permissive notice; copyright Yann Collet, preserve notices and mark changes. Repository LICENSE is BSD-2-Clause.
- gxhash: MIT; copyright Olivier Giniaux; preserved LICENSE
- fips: NIST US Government publication; no third-party rights clearance inferred
- sp800: NIST US Government publication; no third-party rights clearance inferred
- rfc: IETF Trust copyright and BCP 78; consult copyright notice in original; summary only

FIPS 197-upd1 is the May 9, 2023 editorial update. FIPS 186-5 is February 3,
2023; its [official status page](https://csrc.nist.gov/pubs/fips/186-5/final)
reports potential updates/errata. The notes do not claim errata reconciliation or
FIPS validation. SP 800-38D is November 2007. RFC 8439 is June 2018; RFC 7748
January 2016; RFC 8446 August 2018. These are pinned editions, not a claim that
every current erratum has been incorporated.

See [hash requirements](hash_requirements.md), [crypto requirements](crypto_requirements.md),
and [evidence contract](evidence_contract.md). These are refinement of the user's
requested algorithms and 99% branch target, not selection of unrelated features.
