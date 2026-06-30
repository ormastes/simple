-- Fat32.Basic — Lean 4 formal model of the SimpleOS FAT32 filesystem.
--
-- Source-fidelity map (each Lean definition mirrors a .spl function/struct):
--
--   Fat32Bpb              ← struct Fat32Bpb in fat32.spl
--   FatTable              ← modelled as Array Nat (FAT entries, 28-bit values)
--   clusterToLba          ← fn cluster_to_lba(bpb, cluster)
--   isEoc                 ← FAT32 EOC marker: 0x0FFFFFF8..0x0FFFFFFF
--   isFree                ← FAT32 free-cluster marker: 0x00000000
--   chainWalkGuarded      ← GUARDED variant of wave-4b read_cluster_chain walk
--   dirEntry83Name        ← 8.3 name bytes from a 32-byte directory entry buffer
--   dirEntry83NameDecode  ← decode 11 bytes → "BASENAME.EXT" text
--   dirEntry83NameEncode  ← encode "BASENAME.EXT" → 11 bytes
--   clusterCount          ← ⌈fileSize / clusterSize⌉ cluster span
--
-- FINDINGs (implementation gaps in fat32.spl, wave-4b/4c):
--
--   FINDING-T1: read_cluster_chain is described in wave-4b but NOT implemented.
--               The read() fn only reads from root_dir_data (first cluster
--               cached at mount time).  No FAT table is consulted during read.
--               → Lean models the GUARDED variant; the real code lacks the guard.
--
--   FINDING-T2: No allocation function exists in fat32.spl (write() is a stub
--               returning -1).  The no-cross-link invariant cannot be verified
--               against a real allocator; we prove it for the abstract model.
--
--   FINDING-T3: No cycle-detection guard is present in the .spl code.
--               The guarded walk (chainWalkGuarded) adds a fuel/visited-set
--               parameter absent from the real code.  The real code would loop
--               infinitely on a cyclic FAT.

namespace Fat32.Basic

-- ===========================================================================
-- BPB (BIOS Parameter Block) geometry
-- Mirrors struct Fat32Bpb in fat32.spl (fields used by cluster_to_lba).
-- ===========================================================================

structure Fat32Bpb where
  bytesPerSector    : Nat   -- bytes_per_sector   (must be 512 in practice)
  sectorsPerCluster : Nat   -- sectors_per_cluster (power of 2, ≥ 1)
  reservedSectors   : Nat   -- reserved_sectors
  numFats           : Nat   -- num_fats
  fatSize32         : Nat   -- fat_size_32 (sectors per FAT copy)
  rootCluster       : Nat   -- root_cluster (≥ 2)
  deriving Repr

-- Well-formedness: the geometry must be non-degenerate.
def Fat32Bpb.wf (b : Fat32Bpb) : Prop :=
  b.bytesPerSector > 0 ∧
  b.sectorsPerCluster > 0 ∧
  b.numFats > 0 ∧
  b.fatSize32 > 0 ∧
  b.rootCluster ≥ 2

-- ===========================================================================
-- FAT table model
-- FatTable is indexed by cluster number (0-based).  Entry values:
--   0x00000000          → free cluster
--   0x00000001          → reserved (never assigned)
--   0x00000002..        → next cluster in chain
--   0x0FFFFFF8..0x0FFFF → end-of-chain (EOC)
--   0x0FFFFFF7          → bad cluster
-- ===========================================================================

abbrev ClusterIdx := Nat
abbrev FatEntry   := Nat   -- 28-bit value (high 4 bits masked away in FAT32)

-- FAT32 EOC range: 0x0FFFFFF8 to 0x0FFFFFFF
def FAT32_EOC_LOW  : Nat := 0x0FFFFFF8
def FAT32_EOC_HIGH : Nat := 0x0FFFFFFF
def FAT32_FREE     : Nat := 0x00000000
def FAT32_BAD      : Nat := 0x0FFFFFF7

def isEoc (e : FatEntry) : Bool := FAT32_EOC_LOW ≤ e && e ≤ FAT32_EOC_HIGH
def isFree (e : FatEntry) : Bool := e == FAT32_FREE
def isBad  (e : FatEntry) : Bool := e == FAT32_BAD
def isValidChainLink (e : FatEntry) : Bool :=
  e ≥ 2 && e < FAT32_EOC_LOW && ¬isBad e

-- A FatTable is a finite map cluster → entry.
-- We use Array here (indexed by cluster number).
structure FatTable where
  entries : Array FatEntry
  deriving Repr, Inhabited

def FatTable.get (fat : FatTable) (c : ClusterIdx) : FatEntry :=
  fat.entries.getD c FAT32_EOC_LOW  -- out-of-range reads return EOC (safe)

-- ===========================================================================
-- Cluster chain walk (GUARDED variant)
-- FINDING-T1, FINDING-T3: the real wave-4b code does not walk the FAT table
-- and has no cycle-detection.  This guarded version adds a fuel counter that
-- strictly decreases, guaranteeing termination.
-- ===========================================================================

-- chainWalkGuarded fat start fuel : collect the cluster list from 'start',
-- following FAT chain entries, stopping at EOC or when fuel reaches 0.
-- The fuel upper bound is fat.entries.size, which is finite.
def chainWalkGuarded (fat : FatTable) (start : ClusterIdx) (fuel : Nat) : List ClusterIdx :=
  match fuel with
  | 0       => []          -- fuel exhausted (cycle guard or length limit)
  | fuel+1  =>
    let e := fat.get start
    if isEoc e then
      [start]              -- end of chain
    else if isFree e || isBad e then
      []                   -- corrupt / free cluster mid-chain
    else if isValidChainLink e then
      start :: chainWalkGuarded fat e fuel
    else
      []

-- ===========================================================================
-- Cluster-to-LBA arithmetic
-- Mirrors fn cluster_to_lba(bpb, cluster) in fat32.spl:
--   fat_region  = reserved_sectors + num_fats * fat_size_32
--   data_offset = (cluster - 2) * sectors_per_cluster
--   lba         = fat_region + data_offset
-- ===========================================================================

def clusterToLba (b : Fat32Bpb) (cluster : Nat) : Nat :=
  let fatRegion  := b.reservedSectors + b.numFats * b.fatSize32
  let dataOffset := (cluster - 2) * b.sectorsPerCluster
  fatRegion + dataOffset

-- ===========================================================================
-- 8.3 directory entry name
-- Mirrors the directory-entry scan in _find_root_entry (fat32.spl lines 316-372).
-- A raw 32-byte directory entry has the name at bytes 0-10 (8 base + 3 ext).
-- ===========================================================================

-- Extract the 11 name bytes from an entry buffer (bytes 0-10).
def dirEntry83Name (entry : Array UInt8) : Array UInt8 :=
  (entry.extract 0 11)

-- Encode "BASENAME.EXT" (≤12 chars) to FAT32 8.3 bytes (11-element array).
-- Rules: pad base with spaces (0x20) to 8 bytes; pad ext to 3 bytes; no dot stored.
def encode83 (name : String) : Array UInt8 :=
  let parts := name.splitOn "."
  let base  := (parts.getD 0 "").toUpper
  let ext   := (parts.getD 1 "").toUpper
  let padArr (s : String) (n : Nat) : Array UInt8 :=
    let chars := s.toList.map (fun c => c.toNat.toUInt8)
    let bytes : Array UInt8 := Array.mk chars
    let truncated := bytes.extract 0 (min bytes.size n)
    let padLen := n - truncated.size
    truncated ++ (List.replicate padLen (0x20 : UInt8) |> Array.mk)
  padArr base 8 ++ padArr ext 3

-- Decode 11 FAT32 name bytes back to "BASE.EXT" (trimming trailing spaces).
def decode83 (raw : Array UInt8) : String :=
  let trim (a : Array UInt8) : String :=
    let stripped := a.toList.reverse.dropWhile (· == 0x20) |>.reverse
    String.ofList (stripped.map (fun b => Char.ofNat b.toNat))
  let base := trim (raw.extract 0 8)
  let ext  := trim (raw.extract 8 11)
  if ext.isEmpty then base else base ++ "." ++ ext

-- ===========================================================================
-- Cluster-count arithmetic
-- How many clusters does a file of fileSize bytes span, given clusterSize bytes/cluster?
-- Formula: ⌈fileSize / clusterSize⌉  (0 for empty files)
-- ===========================================================================

def clusterCount (fileSize : Nat) (clusterSize : Nat) : Nat :=
  if clusterSize == 0 then 0
  else (fileSize + clusterSize - 1) / clusterSize

-- ===========================================================================
-- Allocation model (abstract)
-- FINDING-T2: no real allocator in fat32.spl.  We model an abstract allocator
-- that hands out clusters from a free list, to state the no-cross-link invariant.
-- ===========================================================================

-- A chain set is the set of clusters claimed by one file's chain.
def chainSet (clusters : List ClusterIdx) : List ClusterIdx := clusters

-- Two chains are disjoint if they share no cluster.
def chainsDisjoint (a b : List ClusterIdx) : Prop :=
  ∀ c, c ∈ a → c ∉ b

-- A FAT is cross-link-free if every pair of distinct EOC-terminated chains
-- starting at different clusters is disjoint.
def crossLinkFree (fat : FatTable) (maxFuel : Nat) (starts : List ClusterIdx) : Prop :=
  ∀ i j : Fin starts.length,
    i ≠ j →
    chainsDisjoint
      (chainWalkGuarded fat (starts.get i) maxFuel)
      (chainWalkGuarded fat (starts.get j) maxFuel)

end Fat32.Basic
