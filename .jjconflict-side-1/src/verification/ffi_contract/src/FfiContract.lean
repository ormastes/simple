/-
  FfiContract -- Boundary invariants of Simple's `rt_*` FFI, formalizing the two
  bug classes this session hit.

  PART A — extern symbol resolution (the #97 guard).
    The linker enumerates undefined symbols (`elf_undefined_symbols`,
    src/compiler/70.backend/linker/elf_parser.spl:279; `macho_undefined_symbols`,
    linker/macho_parser.spl:359). The guard's contract: a build is ACCEPTED only
    if every declared `rt_*` extern resolves to a defined symbol; an undefined
    extern REJECTS the build. We prove that in an accepted build every declared
    call target is defined — i.e. no call dispatches through a null/unresolved
    slot.

  PART B — tag/box convention (the #117 double-untag bug class).
    A `RuntimeValue` is a 64-bit word whose low 3 bits are a tag
    (src/runtime/runtime_value.h): TAG_INT=0, TAG_HEAP=1, TAG_FLOAT=2,
    TAG_SPECIAL=3; `TAG_MASK=0x7`. Scalars are shifted left 3 (`rv_from_int i =
    i<<3`); a heap value is an 8-byte-aligned pointer with the low bit set
    (`(ptr)|1`), recovered by `rv_as_heap_ptr v = v & ~7`. We mirror the 3-bit
    shift with Nat arithmetic (`<<3 == *8`, `>>3 == /8`, `&7 == %8`) and prove
    box∘unbox = id per kind AND that a value is EITHER a tagged scalar OR a heap
    pointer, never both — so after one untag the result is a raw pointer (tag
    INT) and a SECOND untag is statically rejected. That is exactly the #117
    invariant: every operation consumes exactly one box level.

  All theorems are proved without `sorry` (std only, no Mathlib).
-/
namespace FfiContract

/-! ## Part A — extern symbol resolution (#97 link guard). -/

/-- A link state: the declared `rt_*` externs and a predicate telling whether a
    symbol is actually defined in the linked image. -/
structure LinkState where
  declared : List String
  defined  : String → Bool

/-- The guard: a build resolves iff every declared extern is defined. Mirrors
    "reject if `undefined_symbols` is non-empty". -/
def resolves (ls : LinkState) : Bool :=
  ls.declared.all (fun s => ls.defined s)

/-- A build is accepted exactly when it resolves. -/
def accepted (ls : LinkState) : Prop := resolves ls = true

/-- No-null-call: in an ACCEPTED build, every declared call target is defined,
    so no `rt_*` dispatch goes through an unresolved (null) symbol. -/
theorem no_null_call (ls : LinkState) (h : accepted ls) (s : String)
    (hs : s ∈ ls.declared) : ls.defined s = true := by
  unfold accepted resolves at h
  rw [List.all_eq_true] at h
  exact h s hs

/-- An undefined declared extern REJECTS the build (contrapositive of the guard):
    such a link state can never be accepted. -/
theorem undefined_rejects (ls : LinkState) (s : String)
    (hs : s ∈ ls.declared) (hu : ls.defined s = false) : ¬ accepted ls := by
  intro h
  have := no_null_call ls h s hs
  rw [hu] at this
  exact Bool.noConfusion this

/-- Adding an already-defined extern preserves acceptance (guard is stable under
    resolved growth). -/
theorem accept_extend_defined (ls : LinkState) (s : String)
    (hdef : ls.defined s = true) (h : accepted ls) :
    accepted { ls with declared := s :: ls.declared } := by
  unfold accepted resolves at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro x hx
  simp only [List.mem_cons] at hx
  cases hx with
  | inl he => subst he; exact hdef
  | inr ht => exact h x ht

/-! ## Part B — tag / box convention (#117 double-untag). -/

-- Tag constants, mirroring runtime_value.h. `TAG_MASK = 7` = low 3 bits.
def TAG_MASK    : Nat := 7
def TAG_INT     : Nat := 0
def TAG_HEAP    : Nat := 1
def TAG_FLOAT   : Nat := 2
def TAG_SPECIAL : Nat := 3

-- rv_tag / rv_payload: `v & 7` and `v >> 3`, modelled as `% 8` and `/ 8`.
def rvTag     (v : Nat) : Nat := v % 8
def rvPayload (v : Nat) : Nat := v / 8

-- rv_from_tag_payload: `(payload << 3) | tag`, modelled as `payload*8 + tag`.
def rvFromTagPayload (tag payload : Nat) : Nat := payload * 8 + tag

/-- Tag round-trips out of a packed word (for any 3-bit tag). -/
theorem tag_of_packed (tag payload : Nat) (h : tag < 8) :
    rvTag (rvFromTagPayload tag payload) = tag := by
  unfold rvTag rvFromTagPayload; omega

/-- Payload round-trips out of a packed word. -/
theorem payload_of_packed (tag payload : Nat) (h : tag < 8) :
    rvPayload (rvFromTagPayload tag payload) = payload := by
  unfold rvPayload rvFromTagPayload; omega

/-! ### Scalar (int) kind: box = `i<<3`, unbox = `v>>3`, tag = INT. -/

def rvFromInt (i : Nat) : Nat := i * 8          -- i << 3, tag bits = 0 = TAG_INT
def rvToInt   (v : Nat) : Nat := v / 8          -- v >> 3

/-- box∘unbox = id for the int kind. -/
theorem int_roundtrip (i : Nat) : rvToInt (rvFromInt i) = i := by
  unfold rvToInt rvFromInt; omega

/-- An int-boxed value carries tag INT. -/
theorem int_tag (i : Nat) : rvTag (rvFromInt i) = TAG_INT := by
  unfold rvTag rvFromInt TAG_INT; omega

/-! ### Heap kind: box = `ptr|1` (aligned ptr), unbox = `v & ~7`, guarded on
     tag = HEAP. Alignment hypothesis `ptr % 8 = 0` mirrors 8-byte object
     alignment (`MIN_HEAP_ADDR`, `rv_as_heap_ptr` masks the low 3 bits). -/

def boxHeap (ptr : Nat) : Nat := ptr + TAG_HEAP  -- ptr | 1 when ptr is aligned

/-- Unbox a heap value: applicable ONLY when the tag is HEAP; strips the tag.
    Returns `none` when the tag is not HEAP — i.e. the operation is rejected on a
    non-heap word. This is the single-box-level consumption guard. -/
def unboxHeap (v : Nat) : Option Nat :=
  if rvTag v = TAG_HEAP then some (v - rvTag v) else none

/-- A heap-boxed aligned pointer carries tag HEAP. -/
theorem boxHeap_tag (ptr : Nat) (h : ptr % 8 = 0) :
    rvTag (boxHeap ptr) = TAG_HEAP := by
  unfold rvTag boxHeap TAG_HEAP; omega

/-- box∘unbox = id for the heap kind (given 8-byte alignment). -/
theorem heap_roundtrip (ptr : Nat) (h : ptr % 8 = 0) :
    unboxHeap (boxHeap ptr) = some ptr := by
  unfold unboxHeap
  rw [boxHeap_tag ptr h, if_pos rfl]
  simp [boxHeap, TAG_HEAP]

/-- A raw (untagged) aligned pointer has tag INT, NOT HEAP: a scalar/pointer word
    is never simultaneously both kinds. This is tag disjointness. -/
theorem raw_ptr_tag_int (ptr : Nat) (h : ptr % 8 = 0) :
    rvTag ptr = TAG_INT := by
  unfold rvTag TAG_INT; omega

/-- No double-untag: the result of `unboxHeap` is a raw aligned pointer whose tag
    is INT, so a SECOND `unboxHeap` is rejected (`none`). Every unbox consumes
    exactly one box level; you can never untag twice. This is the #117 invariant.-/
theorem no_double_untag (ptr : Nat) (h : ptr % 8 = 0) :
    unboxHeap ptr = none := by
  unfold unboxHeap
  rw [raw_ptr_tag_int ptr h]
  simp [TAG_INT, TAG_HEAP]

/-- Composed statement of #117: after boxing then unboxing once, the recovered
    pointer can NEVER be unboxed again. -/
theorem unbox_result_not_reboxable (ptr : Nat) (h : ptr % 8 = 0) :
    ∀ w, unboxHeap (boxHeap ptr) = some w → unboxHeap w = none := by
  intro w hw
  rw [heap_roundtrip ptr h] at hw
  simp only [Option.some.injEq] at hw
  subst hw
  exact no_double_untag ptr h

/-- Tag uniqueness: a word cannot present as two different kinds at once
    (INT and HEAP are distinct tags), so kind dispatch is unambiguous. -/
theorem tag_int_ne_heap : TAG_INT ≠ TAG_HEAP := by decide

theorem int_never_heap (i : Nat) : rvTag (rvFromInt i) ≠ TAG_HEAP := by
  rw [int_tag]; exact tag_int_ne_heap

end FfiContract
