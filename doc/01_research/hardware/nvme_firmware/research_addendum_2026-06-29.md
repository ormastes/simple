# NVMe SSD Firmware Architecture — Research Addendum (2026-06-29)

This addendum **extends** the main report
(`doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md`,
condensed in `nvme_ssd_firmware_architecture_tldr.md`). It records corrections
surfaced by an adversarial verification pass plus deep-research extensions, and
consolidates authoritative sources. It does not replace the main report.

> Scope note: at the time of writing only the TL;DR
> (`nvme_ssd_firmware_architecture_tldr.md`) is present on disk; the full report
> file is referenced but absent. Corrections below are written against the
> report's load-bearing claims and the surviving TL;DR text so they can be
> applied when the full report is restored.

## Corrections to the main report

| Claim | Verdict | Correction | Source |
|---|---|---|---|
| NVMe spec family has four main document categories (base, command-set, transport, management). | Corrected (high) | There are **five** top-level categories: Base, Command Set, Transport, **Boot**, and Management Interface. The NVMe Boot Specification is a primary document, not a sub-component. | [1] |
| Only three NVMe command sets exist: ZNS, KV, Computational Programs. | Corrected (high) | As of the NVMe 2.3 set (2025-08-05) there are **five** I/O command sets: NVM (Rev 1.2), Zoned Namespaces (Rev 1.4), Key Value (Rev 1.3), Computational Programs (Rev 1.2), and **Subsystem Local Memory** (Rev 1.2, new 2024). NVM and SLM were omitted. | [2][1] |
| NVMe supports only PCIe transport. | Corrected (high) | NVMe defines host↔NVM communication across **multiple transports**: PCIe (local) plus NVMe-oF over RDMA, TCP, and Fibre Channel. | [1][5] |
| The SPDK NVMe driver I/O path is "lock-minimized." | Corrected (high) | The I/O path is **lock-free**, not merely lock-minimized: "Queue pairs contain no locks or atomics" and "The NVMe driver takes no locks in the I/O path." Single-thread-per-qpair is an unenforced caller requirement. | [7] |
| Dirty-shutdown recovery rebuilds L2P from **per-band** P2L. | Corrected (high) | Modern SPDK FTL rebuilds L2P from P2L stored in **both bands and chunks**. For **open** bands the P2L lives in a separate cache-device metadata region, not inline at the band tail (closed bands keep P2L in tail metadata); open chunks may restore from VSS DIX metadata. | [8] |
| FTL persists six metadata types (superblock, L2P, band state, valid map, P2L, trim). | Corrected (high) | A **seventh** type is missing: Chunk/zone metadata (per-unit write pointer + lifecycle state, DRAM-cached and mirrored). State nomenclature differs by spec — OCSSD chunks use FREE/OPEN/CLOSED/OFFLINE; ZNS zones use Empty/Implicitly-Opened/Explicitly-Opened/Closed/Full/Offline. Do **not** attribute "OPEN/FREE/CLOSE" to ZNS. | [8][3] |
| FAST is "fully-associative log-block hybrid mapping." | Corrected (high) | FAST = **Fully-Associative Sector Translation**. It is a log-buffer/log-block hybrid FTL, but the full-associativity governs how log-block *sectors* map (any log-block sector can serve any data block), not log blocks as units. | [11] |
| FAST was a conference paper (implied by "Lee et al."). | Corrected (high) | FAST appeared in the **journal** ACM Transactions on Embedded Computing Systems (TECS) Vol. 6 No. 3, Art. 18, **July 2007** (DOI 10.1145/1275986.1275990), authored by Lee, Park, Chung, Lee, Park, Song. | [11] |
| FSCQ machine-checks crash recovery (implying a Lean substrate alongside the report's Lean4 plan). | Corrected (high) | FSCQ and Crash Hoare Logic are implemented in **Coq, not Lean**. No FSCQ-scope Lean4 crash-consistency file-system verifier exists in published literature as of mid-2026; the space remains Coq-centric (FSCQ, DFSCQ, Armada). | [18][19] |
| Veil is a Lean-based storage/crash-consistency verification framework. | Corrected (high) | Veil (CAV 2025, NUS) targets **distributed protocol / state-transition-system** verification (consensus, replication), not storage or crash-consistency specifically. | [21][22] |
| Cosmos+ OpenSSD provides full NVMe support with a named "low-level scheduler" component. | Corrected (high) | Cosmos+ implements only a **subset** of the NVMe command set (research prototype, not a compliant endpoint). Documented firmware components are PCIe-interface, flash-controller-interface, and sample FTLs (GreedyFTL/TutorialFTL/DummyFTL) — there is **no separately named scheduler**. | [34] |
| LightNVM / Open-Channel SSD is an active host-side parallelism path. | Corrected (high) | LightNVM was deprecated and **removed in Linux 5.15 (2021)** (~13.6k lines); OCSSD 1.x/2.0 never entered the NVMe spec proper and were superseded by **NVMe ZNS**. | [36] |
| FastCheck is a standalone system from a paper titled "FastCheck." | Corrected (med) | The paper is **"Crash Recovery in FAST FTL"** (Moon, Lim, Park, Lee; SEUS 2010, Springer LNCS 6399, pp. 13–22). "FastCheck" names the checkpoint-based recovery algorithm within it, not the paper. | [14] |
| eBPF "extends privileged kernels" (sandbox framing). | Clarified (high) | Accurate, but loading eBPF requires privilege by default (**root / CAP_BPF**); unprivileged eBPF exists but is disabled by default and heavily restricted. The verifier is **static** (load-time), not a runtime guard. | [29] |

**Claims confirmed, not corrected (selected load-bearing items):** the SSD
power-fault failure taxonomy [23]; DFTL demand-based caching with a flash-resident
global map [10]; SPDK band-based, P2L+sequence-id dirty-shutdown recovery [8];
Protothreads as stackless, OS-optional, ~2 bytes/thread [25]; FSCQ + Crash Hoare
Logic proving recovery under arbitrary crash/reboot sequences [19]; FastCheck
periodic checkpointing over FAST's FIFO log order [14][17]. Notably, the
verification pass **refuted** the research's concern that GeckoFTL's "lazy
recovery with checkpoints" framing was wrong: the SIGMOD 2016 paper itself states
it "presents a lazy recovery algorithm based on checkpoints that removes this
contention between recovery time and write-amplification," and "lazy recovery" is
GeckoFTL's own term — distinct from the separate "LazyFTL" baseline it compares
against. The main report's GeckoFTL characterization therefore **stands** [15][16].

## Extended findings by topic

### NVMe specification family (2023–2026)
- The current Base spec is **Revision 2.3**, ratified 2025-08-05; the whole family was re-released that date [1].
- Flash Memory Summit 2024 introduced 3 new specs (Boot, Subsystem Local Memory, Computational Programs) plus 8 updates, adding controller live migration, host-directed data placement, Key-Per-I/O encryption, and NVMe-oF zoning [4].
- The Computational Programs Command Set (Rev 1.0, Dec 2023 → Rev 1.2, 2025) standardizes discovering, downloading, and executing programs on the device to cut data movement [2].
- NVMe-oF expanded to a Fibre Channel Transport spec, reaching traditional FC SANs beyond RDMA/TCP [5].
- ZNS performance research is active: "Performance Characterization of NVMe Flash Devices with ZNS" (arXiv 2310.19094, Oct 2023) and ConfZNS++ (SYSTOR 2024) track adoption in file systems, KV stores, and databases [6].

### SPDK NVMe driver + FTL
- The driver is a passive, poll-mode user-space C library that spawns **no** threads; work runs in the caller's context on `spdk_nvme_qpair_process_completions()` [7].
- In-DRAM L2P is bounded (default ~2 GiB most-recently-used) with the remainder paged to a write-back cache device; cache devices with VSS DIX can restore open chunks without the separate P2L log [8].
- Submission queues may be placed in the controller's CMB (BAR space); completion queues stay in host DRAM, matching the NVMe spec [7].
- The NVMe spec allows up to 65,535 I/O queue pairs but real devices expose ~32–128; SPDK notes full throughput is reachable with a single qpair at sufficient depth [7].

### FTL mapping strategies + learned FTL
- DFTL (Gupta, Kim, Urgaonkar — ASPLOS 2009) keeps the full page map in flash (GMT) and caches only active entries (CMT); a CMT miss costs an extra "double-read" before the data read [10].
- Tradeoffs: page-level needs ~20 GB DRAM for a 10 TB drive at 4 KB/8 B but minimizes random-write WA; block-level is compact but forces costly merges; hybrid log-block sits between; demand-based trades DRAM for double-read latency [10].
- **LeaFTL** (Sun et al. — ASPLOS 2023) uses runtime linear regression to compress mapping entries into learned segments: 2.9× memory reduction, 1.4× throughput [12].
- **LearnedFTL** (Wang et al. — HPCA 2024) adds learned PPN prediction over a demand CMT, cutting double reads up to 55.5% and P99 latency 2.9×–12.2× vs TPFTL/LeaFTL [13].
- Both deliberately use linear models, not neural nets, because embedded-ARM controllers need bounded inference time — so "neural-network FTL mapping" is not the mainstream approach [12][13].

### Crash-recovery techniques
- "Crash Recovery in FAST FTL" (SEUS 2010) exploits FAST's FIFO log-block order with periodic checkpoints to avoid full-scan recovery [14].
- GeckoFTL (Dayan, Bonnet, Idreos — SIGMOD 2016) replaces the Page Validity Bitmap with a Logarithmic Gecko (LSM-like) structure: 95% RAM reduction and a checkpoint-bounded recovery scan (51% reduction) at negligible WA [15][16].
- The checkpoint + WAL + per-band/chunk P2L pattern is an **engineering** design realized in SPDK FTL; no single academic paper coins it as a named technique [8].
- An unrelated 2025 IEEE paper also named "FastCheck" concerns DNN-training checkpointing — not FTL — and should not be conflated [14].

### Crash-consistency formal verification
- FSCQ (Chen, Ziegler, Chajed, Chlipala, Kaashoek, Zeldovich — SOSP 2015) is the first file system with a machine-checked proof (in Coq) covering crashes via Crash Hoare Logic, whose triples carry a crash condition and recovery procedure [19].
- DFSCQ (SOSP 2017) extends FSCQ with a tree specification; still Coq-based [18].
- Lean 4 (Apache-2.0; de Moura et al.) is both a dependent-type prover and a functional language that compiles to C [20].
- Veil's small trusted base comes from Loom (one executable spec shared by model checker and SMT) and Lean-SMT (SMT proofs re-checked in Lean's kernel) [22].
- No Lean4 crash-consistency file-system verifier of FSCQ's scope was found in 2024–2026 sources — a real gap the report's Lean4 plan must own rather than inherit from FSCQ [18].

### SSD power-fault reliability
- Zheng, Tucek, Qin, Lillibridge (FAST '13) injected >3,000 power-fault cycles into 15 commodity SSDs from 5 vendors; **13/15** showed bit corruption, shorn writes, unserializable writes, metadata corruption, or total device failure [23][24].
- The study used a purpose-built hardware power-fault injection framework and framed power faults as a dependability gap largely ignored in storage research [23].

### Stackless coroutines for firmware
- Protothreads (Dunkels, Schmidt, Voigt, Ali — SenSys 2006) are stackless, OS-optional, ~2 bytes/thread; the known caveat — automatic locals do not survive a blocking wait — is inherent to the state-machine transform [25][26].
- 2024–2025 work (CACS, SC 2025) challenges the assumption that stackful coroutines inherently cost more context-switch overhead, via call-site register-set minimization [28].
- Stackless coroutines compile to synchronous state machines and run on constrained targets (WebAssembly, SPIR-V) where stackful ones cannot; Rust async/await, C++20 coroutines, and a Zig proposal all follow this model [27].

### eBPF sandbox model + generational handles
- The eBPF verifier runs ~4 static passes (CFG validation, register-state tracking across branches, optimization/inlining, codegen); BTF enables multiple source languages; map helper calls are rewritten to direct implementation calls [29].
- Bounded loops (since Linux 5.3) extended with `bpf_loop`/`bpf_for` kfuncs for arbitrary-size loops while preserving termination guarantees [30].
- Generational-index handles (index + monotonically increasing generation) defeat the ABA/use-after-free problem; Rust `slotmap` and `generational-arena` are production implementations, the latter fully safe (no `unsafe`); the pattern traces to Catherine West's RustConf 2018 ECS keynote [31].

### Open SSD platforms + manycore firmware
- **DeepFlash** (Zhang, Kwon, Swift, Jung — FAST '20) is a manycore SSD firmware design with a many-to-many threading model across dozens of lightweight cores, a three-stage pipeline (Queue-gather → Trans-apply/FTL → Flash-scatter), targeting >1 MIOPS and ~4.5 GB/s — directly addressing the firmware compute bottleneck NVMe parallelism exposes [32].
- **Cosmos+ OpenSSD** (Kwak et al., ACM TOS 2020) is an FPGA prototype (Zynq-7000 XC7Z045, dual Cortex-A9, up to 2 TB NAND) with PCIe/flash-controller interface firmware and sample FTLs (GreedyFTL/TutorialFTL/DummyFTL); it implements only a **subset** of the NVMe command set [33][34].
- **LightNVM** (Bjørling et al., FAST '17) introduced the Physical Page Address (PPA) interface exposing channel/parallel-unit parallelism to the host; merged in Linux 4.4 but **removed in Linux 5.15 (2021)**, superseded by ZNS [35][36].
- **ZNS** is part of NVMe 2.0: sequential-write-only zones (read-any-order) eliminate device-side GC write amplification while the device keeps ECC/reliability. The model intentionally mirrors SMR ZBC/ZAC for a unified software stack [37].
- ZNS ecosystem: WD Ultrastar DC ZN540 hardware, ZenFS (RocksDB plugin), io_uring passthrough, and research lines ZNS+ (OSDI '21) and eZNS (OSDI '23) [38][39].

## Verification of load-bearing claims

| Claim (adversarially verified) | Verdict | Confidence | Source |
|---|---|---|---|
| Power-fault study: 15 SSDs, >3,000 cycles, 5 named failure modes (13/15 failed). | Confirmed | High | [23][24] |
| FAST = fully-associative sector translation; overwrites go to any log block, reducing thrashing vs BAST. | Confirmed | High | [11] |
| DFTL is demand-based: active page-map entries cached in RAM, full map in flash. | Confirmed | High | [10] |
| SPDK FTL rebuilds L2P from per-band/chunk P2L + sequence IDs after dirty shutdown. | Confirmed | High | [8] |
| Protothreads: stackless, OS-optional, ~2 bytes/thread overhead. | Confirmed | High | [25] |
| FSCQ machine-checks crash recovery via Crash Hoare Logic over arbitrary crash/reboot sequences. | Confirmed | High | [19] |
| GeckoFTL uses lazy recovery with checkpoints to remove the WA-vs-recovery-time contention. | Confirmed | High | [15][16] |
| FastCheck adds periodic checkpointing to FAST-style log-page mapping for crash recovery. | Confirmed | High | [14][17] |
| SPDK NVMe I/O path is lock-free (not lock-minimized). | Confirmed | High | [7] |
| Open-band/chunk P2L lives in a separate cache-device region (not inline at band tail). | Confirmed | High | [8] |
| NVMe spec family has five document categories (Boot omitted from report). | Corrected | High | [1] |
| Five NVMe command sets exist (NVM + SLM omitted from report). | Corrected | High | [1][2] |
| NVMe supports multiple transports (PCIe/RDMA/TCP/FC). | Corrected | High | [1][5] |
| FTL metadata includes a seventh chunk/zone type; ZNS state names differ from OCSSD. | Corrected | High | [8][3] |
| FAST naming ("sector translation") and venue (TECS journal, 2007). | Corrected | High | [11] |

## Consolidated references

1. NVM Express, "NVM Express Specifications" (Guide to the NVMe 2.3 set; specs released 2025-08-05). https://nvmexpress.org/specifications/
2. NVM Express, "Computational Programs Command Set Specification." https://nvmexpress.org/specification/computational-programs-command-set/
3. NVM Express, "Zoned Namespaces (ZNS) Command Set Specification." https://nvmexpress.org/specification/nvme-zoned-namespaces-zns-command-set-specification/
4. StorageNewsletter, "NVMe: 3 New and 8 Updated Specs to Unify AI, Cloud, Client and Enterprise Storage" (Oct 2024). https://www.storagenewsletter.com/2024/10/18/nvme-3-new-and-8-updated-specs-to-unify-ai-cloud-client-and-enterprise-storage/
5. Phoronix, "NVMe 2.1 Specifications Published" (Aug 2024). https://www.phoronix.com/news/NVMe-2.1-Specifications
6. "Performance Characterization of NVMe Flash Devices with Zoned Namespaces (ZNS)," arXiv:2310.19094 (Oct 2023). https://arxiv.org/pdf/2310.19094
7. SPDK, "NVMe Driver." https://spdk.io/doc/nvme.html
8. SPDK, "Flash Translation Layer." https://spdk.io/doc/ftl.html
9. SPDK, "User Space Drivers." https://spdk.io/doc/userspace.html
10. Gupta, Kim, Urgaonkar, "DFTL: A Flash Translation Layer Employing Demand-based Selective Caching of Page-level Address Mappings," ASPLOS 2009. https://dl.acm.org/doi/10.1145/1508284.1508271
11. Lee, Park, Chung, Lee, Park, Song, "A Log Buffer-Based Flash Translation Layer Using Fully-Associative Sector Translation," ACM TECS Vol. 6 No. 3, July 2007. https://dl.acm.org/doi/10.1145/1275986.1275990
12. Sun, Li, Sun, Sun, Vucinic, Huang, "LeaFTL: A Learning-Based Flash Translation Layer for SSDs," ASPLOS 2023. https://arxiv.org/abs/2301.00072
13. Wang, Lin, Wu, Jiang, Zhang, Mao, "LearnedFTL: A Learning-based Page-level FTL for Reducing Double Reads in Flash-based SSDs," HPCA 2024. https://arxiv.org/html/2303.13226v2
14. Moon, Lim, Park, Lee, "Crash Recovery in FAST FTL," SEUS 2010, Springer LNCS 6399, pp. 13–22. https://link.springer.com/chapter/10.1007/978-3-642-16256-5_4 (record: https://inria.hal.science/hal-01055380v1)
15. Dayan, Bonnet, Idreos, "GeckoFTL: Scalable Flash Translation Techniques for Very Large Flash Devices," SIGMOD 2016. https://dl.acm.org/doi/10.1145/2882903.2915219
16. GeckoFTL paper PDF (author copy). https://nivdayan.github.io/GeckoFTLPaper.pdf
17. "A Crash Recovery Scheme for a Hybrid Mapping FTL in NAND Flash Storage Devices," Electronics 10(3):327, MDPI. https://www.mdpi.com/2079-9292/10/3/327
18. FSCQ project page, MIT CSAIL. http://css.csail.mit.edu/fscq/
19. Chen, Ziegler, Chajed, Chlipala, Kaashoek, Zeldovich, "Using Crash Hoare Logic for Certifying the FSCQ File System," SOSP 2015. https://pdos.csail.mit.edu/papers/fscq:sosp15.pdf
20. de Moura et al., "The Lean 4 Theorem Prover and Programming Language," IJCAR 2021. https://link.springer.com/chapter/10.1007/978-3-030-79876-5_37
21. Pîrlea, Gladshtein, Kinsbruner, Zhao, Sergey, "Veil: A Framework for Automated and Interactive Verification of Transition Systems," CAV 2025. https://link.springer.com/chapter/10.1007/978-3-031-98682-6_2
22. Veil use-case page, lean-lang.org. https://lean-lang.org/use-cases/veil/
23. Zheng, Tucek, Qin, Lillibridge, "Understanding the Robustness of SSDs under Power Fault," USENIX FAST '13. https://www.usenix.org/conference/fast13/technical-sessions/presentation/zheng
24. FAST '13 full paper PDF. https://www.usenix.org/system/files/conference/fast13/fast13-final80.pdf
25. Dunkels, Schmidt, Voigt, Ali, "Protothreads: Simplifying Event-Driven Programming of Memory-Constrained Embedded Systems," SenSys 2006 (PDF). https://dunkels.com/adam/dunkels06protothreads.pdf
26. Protothreads, ACM Proceedings of SenSys 2006. https://dl.acm.org/doi/10.1145/1182807.1182811
27. "A Survey of Asynchronous Programming Using Coroutines in the Internet of Things and Embedded Systems," arXiv:1906.00367. https://arxiv.org/pdf/1906.00367
28. "Stackless vs. Stackful Coroutines: A Comparative Study for RDMA-based Asynchronous Many-Task Runtimes," SC 2025 Workshops. https://dl.acm.org/doi/10.1145/3731599.3767502
29. "The eBPF Runtime in the Linux Kernel," arXiv:2410.00026v2. https://arxiv.org/html/2410.00026v2
30. eBPF Docs, "Verifier." https://docs.ebpf.io/linux/concepts/verifier/
31. fitzgen, "generational-arena" (Rust crate). https://github.com/fitzgen/generational-arena
32. Zhang, Kwon, Swift, Jung, "Scalable Parallel Flash Firmware for Many-core Architectures" (DeepFlash), USENIX FAST '20. https://www.usenix.org/conference/fast20/presentation/zhang-jie
33. Kwak, Lee, Park, Jeong, Song, "Cosmos+ OpenSSD: Rapid Prototype for Flash Storage Systems," ACM TOS Vol. 16 No. 3, July 2020. https://dl.acm.org/doi/10.1145/3385073
34. Cosmos+ Platform Overview, The OpenSSD Project. http://www.openssd-project.org/cosmospl/overview/
35. Bjørling, González, Bonnet, "LightNVM: The Linux Open-Channel SSD Subsystem," USENIX FAST '17. https://www.usenix.org/conference/fast17/technical-sessions/presentation/bjorling
36. Phoronix, "Linux Turning Off The Light — LightNVM To Be Removed" (Aug 2021). https://www.phoronix.com/news/Linux-Dropping-LightNVM
37. "NVMe Zoned Namespaces (ZNS) Devices," Zoned Storage. https://zonedstorage.io/docs/introduction/zns
38. Han et al., "ZNS+: Advanced Zoned Namespace Interface for Supporting In-Storage Zone Compaction," USENIX OSDI '21. https://www.usenix.org/conference/osdi21/presentation/han
39. Min et al., "eZNS: An Elastic Zoned Namespace for Commodity ZNS SSDs," USENIX OSDI '23. https://www.usenix.org/conference/osdi23/presentation/min
40. Open-Channel SSD Specification Revision 2.0. http://lightnvm.io/docs/OCSSD-2_0-20180129.pdf

---
generated by the nvme-fw-research-extend workflow on 2026-06-29
