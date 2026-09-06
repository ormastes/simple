<!-- codex-research -->
# SimpleOS NVFS Submodule Migration — Domain Research

External domain research is not load-bearing for this migration. The relevant source of truth is the local repository architecture: SimpleOS owns the storage stack and already defines FAT32/NVFS/DBFS sharing through a common NVMe lease and `BlockDevice` interface.

The only external operation is repository retirement on GitHub for `ormastes/simple-nvfs`, which is operational cleanup after the local source migration is verified.
