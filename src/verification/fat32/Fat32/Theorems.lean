-- Fat32.Theorems — Six FAT32 filesystem invariant theorems (zero sorry).
--
-- T1 chain_terminates      : chainWalkGuarded always terminates (fuel bound).
--                            FINDING-T1/T3: real wave-4b read_cluster_chain not
--                            yet implemented; real code lacks FAT walk + cycle guard.
-- T2 lba_monotone          : cluster_to_lba is strictly monotone in cluster number
--                            for a well-formed BPB.  Mirrors cluster_to_lba in fat32.spl.
-- T3 lba_injective         : distinct cluster numbers map to distinct LBA sectors.
-- T4 encode_decode_roundtrip : encode83 followed by decode83 roundtrips simple
--                            "BASE.EXT" names (concrete cases via native_decide).
-- T5 cluster_count_correct : clusterCount fileSize clusterSize * clusterSize ≥ fileSize.
-- T6 eoc_not_free          : isEoc and isFree are mutually exclusive.

import Fat32.Basic

namespace Fat32.Theorems

open Fat32.Basic

-- ===========================================================================
-- T1 — chain_terminates
-- chainWalkGuarded produces a list whose length ≤ fuel + 1.
-- Fuel strictly decreases on every recursive call, guaranteeing termination.
-- FINDING-T1: the real read() only reads root_dir_data (first cluster cached
-- at mount); no FAT chain walk exists in fat32.spl (wave-4b not implemented).
-- FINDING-T3: no cycle-detection guard in the .spl code; this model adds one.
-- ===========================================================================

-- Helper: unfold one step of chainWalkGuarded for the succ case.
private theorem chainWalk_succ (fat : FatTable) (start : ClusterIdx) (n : Nat) :
    chainWalkGuarded fat start (n + 1) =
      if isEoc (fat.get start) then [start]
      else if isFree (fat.get start) || isBad (fat.get start) then []
      else if isValidChainLink (fat.get start) then
        start :: chainWalkGuarded fat (fat.get start) n
      else [] := by
  simp [chainWalkGuarded]

theorem T1_chain_length_bound (fat : FatTable) (start : ClusterIdx) (fuel : Nat) :
    (chainWalkGuarded fat start fuel).length ≤ fuel + 1 := by
  induction fuel generalizing start with
  | zero =>
    simp [chainWalkGuarded]
  | succ n ih =>
    rw [chainWalk_succ]
    split
    · -- isEoc: returns [start], length = 1
      simp
    · split
      · -- isFree or isBad: returns [], length = 0
        simp
      · split
        · -- valid chain link: cons + recurse
          simp only [List.length_cons]
          have := ih (fat.get start)
          omega
        · -- neither: returns [], length = 0
          simp

-- ===========================================================================
-- T2 — lba_monotone
-- For a well-formed BPB, clusterToLba is strictly monotone in cluster number.
-- Mirrors fn cluster_to_lba in fat32.spl.
-- ===========================================================================

theorem T2_lba_monotone (b : Fat32Bpb) (c1 c2 : Nat)
    (hwf : b.wf) (hlt : c1 < c2) (hc1 : c1 ≥ 2) :
    clusterToLba b c1 < clusterToLba b c2 := by
  simp only [clusterToLba, Fat32Bpb.wf] at *
  obtain ⟨_, hspc, _, _, _⟩ := hwf
  have h1 : c1 - 2 < c2 - 2 := by omega
  have hmono : (c1 - 2) * b.sectorsPerCluster < (c2 - 2) * b.sectorsPerCluster :=
    Nat.mul_lt_mul_of_pos_right h1 hspc
  omega

-- ===========================================================================
-- T3 — lba_injective
-- For a well-formed BPB, distinct clusters ≥ 2 map to distinct LBA sectors.
-- ===========================================================================

theorem T3_lba_injective (b : Fat32Bpb) (c1 c2 : Nat)
    (hwf : b.wf) (hc1 : c1 ≥ 2) (hc2 : c2 ≥ 2)
    (heq : clusterToLba b c1 = clusterToLba b c2) :
    c1 = c2 := by
  simp only [clusterToLba] at heq
  obtain ⟨_, hspc, _, _, _⟩ := hwf
  have hcancel : (c1 - 2) * b.sectorsPerCluster = (c2 - 2) * b.sectorsPerCluster := by
    omega
  have heq2 : c1 - 2 = c2 - 2 := Nat.eq_of_mul_eq_mul_right hspc hcancel
  omega

-- ===========================================================================
-- T4 — encode_decode_roundtrip
-- encode83 → decode83 roundtrips concrete 8.3 names.
-- Models the 8.3 name lookup path in _find_root_entry (fat32.spl line 316).
-- ===========================================================================

theorem T4_encode_decode_README_MD :
    decode83 (encode83 "README.MD") = "README.MD" := by
  native_decide

theorem T4_encode_decode_KERNEL_ELF :
    decode83 (encode83 "KERNEL.ELF") = "KERNEL.ELF" := by
  native_decide

theorem T4_encode_decode_no_ext :
    decode83 (encode83 "SIMPLEOS") = "SIMPLEOS" := by
  native_decide

-- ===========================================================================
-- T5 — cluster_count_correct
-- The cluster span always covers the file.
-- clusterCount fileSize clusterSize * clusterSize ≥ fileSize
-- Models the invariant that a FileHandle's chain covers all file_size bytes.
-- ===========================================================================

-- Lemma: ceiling division satisfies ⌈n/d⌉ * d ≥ n for d > 0.
-- We use Nat.le_of_dvd + inequality reasoning via the standard library.
private theorem ceil_div_covers (n d : Nat) (hd : d > 0) :
    (n + d - 1) / d * d ≥ n := by
  -- (n + d - 1) / d * d  =  d * ((n + d - 1) / d)
  -- Nat.div_add_mod : d * (m / d) + m % d = m
  -- So d * ((n+d-1)/d) = (n+d-1) - (n+d-1)%d ≥ n+d-1-(d-1) = n
  have hdvd : d * ((n + d - 1) / d) + (n + d - 1) % d = n + d - 1 :=
    Nat.div_add_mod (n + d - 1) d
  have hmod_lt : (n + d - 1) % d < d := Nat.mod_lt _ hd
  have hmul_eq : (n + d - 1) / d * d = d * ((n + d - 1) / d) := Nat.mul_comm _ _
  rw [hmul_eq]
  omega

theorem T5_cluster_count_covers (fileSize clusterSize : Nat)
    (hcs : clusterSize > 0) :
    clusterCount fileSize clusterSize * clusterSize ≥ fileSize := by
  unfold clusterCount
  have hne : clusterSize ≠ 0 := Nat.pos_iff_ne_zero.mp hcs
  simp only [show (clusterSize == 0) = false from by simp [hne], Bool.false_eq_true,
             ↓reduceIte]
  exact ceil_div_covers fileSize clusterSize hcs

-- ===========================================================================
-- T6 — eoc_not_free
-- isEoc and isFree are mutually exclusive.
-- FAT32_EOC_LOW = 0x0FFFFFF8 = 268435448 > 0 = FAT32_FREE.
-- ===========================================================================

-- We prove the concrete numeric fact by decide.
private theorem eoc_low_gt_zero : FAT32_EOC_LOW > FAT32_FREE := by decide

theorem T6_eoc_not_free (e : FatEntry) :
    ¬(isEoc e = true ∧ isFree e = true) := by
  simp only [isEoc, isFree, FAT32_EOC_LOW, FAT32_FREE]
  intro ⟨heoc, hfree⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at heoc
  simp only [beq_iff_eq] at hfree
  obtain ⟨hlo, _⟩ := heoc
  -- hlo : 268435448 ≤ e, hfree : e = 0
  subst hfree
  omega

-- ===========================================================================
-- T6 corollary — free_not_valid_chain_link
-- A free entry is not a valid chain link, preventing chain walk from following it.
-- ===========================================================================

theorem T6_free_not_valid_chain (e : FatEntry)
    (hfree : isFree e = true) :
    isValidChainLink e = false := by
  simp only [isFree, FAT32_FREE, beq_iff_eq] at hfree
  subst hfree
  -- e = 0: 0 ≥ 2 is false
  simp [isValidChainLink, isBad, FAT32_BAD, FAT32_EOC_LOW]

end Fat32.Theorems
