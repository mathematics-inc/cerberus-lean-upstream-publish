/-
  CerbCtypeMeasure — the executable fuel MEASURE of the `Ctype_aux.are_compatible_aux`
  mutual block (are_compatible_aux / are_compatible_params_aux / are_compatible_params),
  hypothesis-free (are-compatible-assumed-set slice, 2026-09-10; charter
  docs/2026-09-10_codex-charter-are-compatible-assumed-set.md).

  THE BLOCK'S RECURSION (frontend/model/ctype_aux.lem): structural descent through
  Array/Function/Pointer/Atomic and parameter lists, plus ONE non-structural step —
  the cross-TU `Struct/Struct` and `Union/Union` arms look the two tags up in the two
  tag tables and recurse into the MEMBER types. Since the slice's body change the
  block threads a path-local list `assumed : list (sym * sym)` of the tag pairs under
  comparison; a hop on a pair already in the list returns `true` (C11 §6.2.7#1's
  "assumed compatible" reading), so every hop adds a pair not yet present.

  THE BOUND, one Nat per entry, computed by the fuel-free wrappers:

    auxGeneral (t1,t2,A) (qs1,ty1) (qs2,ty2)
      = count * weight + lemSize ty1 + lemSize ty2 + 1
    count  = hops t1 t2 A + missing (tagsIn ty1) (occ t1) + missing (tagsIn ty2) (occ t2)
    hops   = #{ (a,b) ∈ occ t1 × occ t2 : (a,b) not `Lem_List.elem` A }
    occ t  = every struct/union tag OCCURRING in a member type of t (in order)
    missing tags o = #{ a ∈ tags : a not `Lem_List.elem` o }
    weight = valsSize t1 + valsSize t2 + 1   (valsSize t = Σ member-type sizes of t)

  Why it bounds the depth (Ctype_aux_lemMeasureProofs.lean proves it):
  - a structural step keeps `count` from growing (same A; the child's tags are a
    sublist of the parent's) and strictly shrinks both sizes;
  - a hop from (Struct s1, Struct s2) into member types (u1, u2) with
    A' = (s1,s2) :: A: the children's tags all occur in the tables (missing = 0), and
    EITHER both s1, s2 occur in the tables — then the pair (a,b) ≈ (s1,s2) of
    occ t1 × occ t2 flips from unassumed to assumed and `hops` drops by ≥ 1 — OR one
    of them does not, and the parent's `missing` was ≥ 1 while the child's is 0 and
    `hops` cannot grow. Either way `count` drops by ≥ 1, and the member sizes are at
    most `valsSize`, so `count' * weight + sizes' + 1 ≤ (count − 1) * weight + weight
    = count * weight < parent`.
  No hypothesis on the tables is needed: the comparator captured in an `Fmap` plays
  no role (a successful lookup only tells us the VALUE is one of the tree's nodes).

  THE CHEAP PATH (the eager-measure lesson, docs/2026-09-07_fuel-measure-cost-record.md):
  `Ctype_aux.are_compatible` runs on every struct-valued store (core_aux.lem:200),
  with two `Struct` types that in a single translation unit satisfy
  `from_same_translation_unit` and return after one digest comparison. `auxBound`
  therefore returns the constant 1 in that case (sufficient: the arm makes no
  recursive call) and evaluates the table-traversing `auxGeneral` only on the
  cross-TU path.

  EQUALITY NOTE: the block tests membership with `Lem_List.elem`, i.e. the model's
  `Eq0 sym` instance (symbol.lem `symbolEqual`: digest and number, description
  ignored). Every lemma here is stated with `Lem_Basic_classes.isEqual` for that
  reason — `==` on `sym` in a hand-written file resolves to a different instance.

  MIRROR-OCAML NOTE: measures and their lemmas are Lean-target artifacts; no OCaml
  text corresponds (the OCaml `are_compatible_aux` is the unbounded `let rec`).
-/

import Ctype
import Symbol
import LemLib
import LemLibTheorems

set_option autoImplicit false

namespace CerbCtypeMeasure

open Lem_Basic_classes (Eq0)

abbrev Table := Fmap sym (CerbLocation.Loc × tag_definition)
abbrev Env := Table × Table × List (sym × sym)
abbrev Member := identifier × (attributes × Option alignment × qualifiers × ctype)
abbrev Param := qualifiers × ctype × Bool

/-! ## Tags occurring in a type -/

mutual
/-- Struct/union tags occurring in a ctype, in order. -/
def tagsIn : ctype → List sym
  | .Ctype _ t => tagsIn_ t
def tagsIn_ : ctype_ → List sym
  | .Void0 => []
  | .Basic _ => []
  | .Array0 ty _ => tagsIn ty
  | .Function (_, rty) ps _ => tagsIn rty ++ tagsInParams ps
  | .FunctionNoParams (_, rty) => tagsIn rty
  | .Pointer _ ty => tagsIn ty
  | .Atomic ty => tagsIn ty
  | .Struct tag => [tag]
  | .Union0 tag => [tag]
  | .Byte => []
def tagsInParams : List Param → List sym
  | [] => []
  | (_, ty, _) :: rest => tagsIn ty ++ tagsInParams rest
end

/-! ## Member types of a tag table: their tags and their sizes -/

def memberTags : List Member → List sym
  | [] => []
  | (_, (_, _, _, ty)) :: rest => tagsIn ty ++ memberTags rest

def flexTags : Option flexible_array_member → List sym
  | none => []
  | some (.FlexibleArrayMember _ _ _ ty) => tagsIn ty

def defTags : tag_definition → List sym
  | .StructDef xs fo => memberTags xs ++ flexTags fo
  | .UnionDef xs => memberTags xs

def pmapTags : Pmap sym (CerbLocation.Loc × tag_definition) → List sym
  | .Empty => []
  | .Node l _ (_, d) r _ => pmapTags l ++ defTags d ++ pmapTags r

/-- Every struct/union tag occurring in a member type of the table. -/
def occ (t : Table) : List sym := pmapTags t.rep

def memberSizes : List Member → Nat
  | [] => 0
  | (_, (_, _, _, ty)) :: rest => ctype.lemSize ty + memberSizes rest

def flexSize : Option flexible_array_member → Nat
  | none => 0
  | some (.FlexibleArrayMember _ _ _ ty) => ctype.lemSize ty

def defSize : tag_definition → Nat
  | .StructDef xs fo => memberSizes xs + flexSize fo
  | .UnionDef xs => memberSizes xs

def pmapValsSize : Pmap sym (CerbLocation.Loc × tag_definition) → Nat
  | .Empty => 0
  | .Node l _ (_, d) r _ => pmapValsSize l + defSize d + pmapValsSize r

/-- The sum of the sizes of every member type of the table. -/
def valsSize (t : Table) : Nat := pmapValsSize t.rep

/-! ## The counters -/

def pairs (l1 l2 : List sym) : List (sym × sym) :=
  l1.flatMap (fun a => l2.map (fun b => (a, b)))

/-- Pairs of occurring tags not yet assumed (membership by the block's own
    `Lem_List.elem`, i.e. the model's symbol equality). -/
def hops (t1 t2 : Table) (A : List (sym × sym)) : Nat :=
  ((pairs (occ t1) (occ t2)).filter (fun q => !(Lem_List.elem q A))).length

/-- Tags of a type that do not occur in the table. -/
def missing (tags o : List sym) : Nat :=
  (tags.filter (fun a => !(Lem_List.elem a o))).length

def weight (t1 t2 : Table) : Nat := valsSize t1 + valsSize t2 + 1

def count (t1 t2 : Table) (A : List (sym × sym)) (tags1 tags2 : List sym) : Nat :=
  hops t1 t2 A + missing tags1 (occ t1) + missing tags2 (occ t2)

/-! ## The measures -/

/-- The general bound of `are_compatible_aux (t1,t2,A) (qs1,ty1) (qs2,ty2)`. -/
def auxGeneral (p : Env) (p0 p1 : qualifiers × ctype) : Nat :=
  match p with
  | (t1, t2, A) =>
    count t1 t2 A (tagsIn p0.2) (tagsIn p1.2) * weight t1 t2
      + ctype.lemSize p0.2 + ctype.lemSize p1.2 + 1

/-- The cheap path: two struct (or two union) tags of the same translation unit are
    decided by the arm itself without a recursive call. -/
def sameTuTags : ctype → ctype → Bool
  | .Ctype _ (.Struct a), .Ctype _ (.Struct b) => from_same_translation_unit a b
  | .Ctype _ (.Union0 a), .Ctype _ (.Union0 b) => from_same_translation_unit a b
  | _, _ => false

/-- THE MEASURE of `are_compatible_aux` (named by the `fuel_measure` declare in
    ctype_aux.lem; the generated binders are `p p0 p1`). -/
def auxBound (p : Env) (p0 p1 : qualifiers × ctype) : Nat :=
  if sameTuTags p0.2 p1.2 then 1 else auxGeneral p p0 p1

/-- THE MEASURE of `are_compatible_params_aux` (binders `env1 lemTail`; `lemTail` is
    the hoisted `function` scrutinee, the pair of parameter lists). -/
def paramsAuxBound (env1 : Env) (lemTail : List Param × List Param) : Nat :=
  match env1 with
  | (t1, t2, A) =>
    count t1 t2 A (tagsInParams lemTail.1) (tagsInParams lemTail.2) * weight t1 t2
      + ctype_.lemSize_aux1 lemTail.1 + ctype_.lemSize_aux1 lemTail.2 + 1

/-- THE MEASURE of `are_compatible_params` (binders `env1 params1 params2`): it calls
    the aux at fuel − 1 on the same lists. -/
def paramsBound (env1 : Env) (params1 params2 : List Param) : Nat :=
  paramsAuxBound env1 (params1, params2) + 1

/-! ## Positivity -/

theorem ctype_lemSize_pos (c : ctype) : 1 ≤ ctype.lemSize c := by
  cases c; simp only [ctype.lemSize]; omega

theorem weight_pos (t1 t2 : Table) : 1 ≤ weight t1 t2 := by
  unfold weight; omega

theorem auxGeneral_pos (p : Env) (p0 p1 : qualifiers × ctype) : 1 ≤ auxGeneral p p0 p1 := by
  obtain ⟨t1, t2, A⟩ := p; simp only [auxGeneral]; omega

theorem auxBound_pos (p : Env) (p0 p1 : qualifiers × ctype) : 1 ≤ auxBound p p0 p1 := by
  unfold auxBound; split
  · exact Nat.le_refl 1
  · exact auxGeneral_pos p p0 p1

theorem auxBound_le_general (p : Env) (p0 p1 : qualifiers × ctype) :
    auxBound p p0 p1 ≤ auxGeneral p p0 p1 := by
  unfold auxBound; split
  · exact auxGeneral_pos p p0 p1
  · exact Nat.le_refl _

theorem auxBound_eq_general {p : Env} {p0 p1 : qualifiers × ctype}
    (h : sameTuTags p0.2 p1.2 = false) : auxBound p p0 p1 = auxGeneral p p0 p1 := by
  unfold auxBound; simp [h]

theorem paramsAuxBound_pos (env1 : Env) (lemTail : List Param × List Param) :
    1 ≤ paramsAuxBound env1 lemTail := by
  obtain ⟨t1, t2, A⟩ := env1; simp only [paramsAuxBound]; omega

theorem paramsBound_pos (env1 : Env) (params1 params2 : List Param) :
    2 ≤ paramsBound env1 params1 params2 := by
  unfold paramsBound; have := paramsAuxBound_pos env1 (params1, params2); omega

/-! ## Filters: monotonicity and strict decrease -/

/-- Filtering by a stronger predicate yields a sublist. -/
theorem filter_sublist_of_imp {α : Type} (P Q : α → Bool) (l : List α)
    (h : ∀ x, Q x = true → P x = true) : (l.filter Q).Sublist (l.filter P) := by
  induction l with
  | nil => exact List.Sublist.refl _
  | cons x xs ih =>
    cases hq : Q x with
    | true =>
      rw [List.filter_cons_of_pos hq, List.filter_cons_of_pos (h x hq)]
      exact ih.cons₂ x
    | false =>
      rw [List.filter_cons_of_neg (by simp [hq])]
      cases hp : P x with
      | true => rw [List.filter_cons_of_pos hp]; exact ih.cons x
      | false => rw [List.filter_cons_of_neg (by simp [hp])]; exact ih

/-- A stronger predicate that rejects some element the weaker one keeps filters
    strictly fewer elements. -/
theorem filter_length_lt_of_imp {α : Type} (P Q : α → Bool) (l : List α)
    (h : ∀ x, Q x = true → P x = true) (w : ∃ x, x ∈ l ∧ P x = true ∧ Q x = false) :
    (l.filter Q).length < (l.filter P).length := by
  induction l with
  | nil => obtain ⟨x, hx, _⟩ := w; exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    obtain ⟨x, hx, hpx, hqx⟩ := w
    rcases List.mem_cons.mp hx with rfl | hx'
    · -- the witness is the head
      rw [List.filter_cons_of_pos hpx, List.filter_cons_of_neg (by simp [hqx]), List.length_cons]
      have := (filter_sublist_of_imp P Q ys h).length_le
      omega
    · have ih' := ih ⟨x, hx', hpx, hqx⟩
      cases hq : Q y with
      | true =>
        rw [List.filter_cons_of_pos hq, List.filter_cons_of_pos (h y hq), List.length_cons,
          List.length_cons]
        omega
      | false =>
        rw [List.filter_cons_of_neg (by simp [hq])]
        cases hp : P y with
        | true => rw [List.filter_cons_of_pos hp, List.length_cons]; omega
        | false => rw [List.filter_cons_of_neg (by simp [hp])]; exact ih'

/-! ## The block's list membership, spelled out -/

/-- `Lem_List.elem` is `listMemberBy (· == ·)` at the `Eq0` instance: one step. -/
theorem elem_cons {α : Type} [Eq0 α] (x y : α) (l : List α) :
    Lem_List.elem x (y :: l) = (Lem_Basic_classes.isEqual x y || Lem_List.elem x l) := rfl

theorem elem_nil {α : Type} [Eq0 α] (x : α) : Lem_List.elem x ([] : List α) = false := rfl

theorem elem_mono {α : Type} [Eq0 α] {x : α} {l : List α} (y : α)
    (h : Lem_List.elem x l = true) : Lem_List.elem x (y :: l) = true := by
  rw [elem_cons, h, Bool.or_true]

theorem elem_true_iff {α : Type} [Eq0 α] (x : α) (l : List α) :
    Lem_List.elem x l = true ↔ ∃ a, a ∈ l ∧ Lem_Basic_classes.isEqual x a = true := by
  induction l with
  | nil => simp [elem_nil]
  | cons y ys ih =>
    rw [elem_cons, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨a, ha, h⟩)
      · exact ⟨y, List.mem_cons_self, h⟩
      · exact ⟨a, List.mem_cons_of_mem y ha, h⟩
    · rintro ⟨a, ha, h⟩
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact Or.inl h
      · exact Or.inr ⟨a, ha', h⟩

/-- Not a member of the longer list, hence not of the shorter. -/
theorem not_elem_of_not_elem_cons {α : Type} [Eq0 α] {x y : α} {l : List α}
    (h : Lem_List.elem x (y :: l) = false) : Lem_List.elem x l = false := by
  cases hl : Lem_List.elem x l with
  | false => rfl
  | true => rw [elem_mono y hl] at h; exact Bool.noConfusion h

/-! ## `missing` and `hops` -/

theorem missing_sublist {l1 l2 o : List sym} (h : l1.Sublist l2) :
    missing l1 o ≤ missing l2 o :=
  (h.filter _).length_le

theorem missing_eq_zero {tags o : List sym} (h : ∀ a, a ∈ tags → Lem_List.elem a o = true) :
    missing tags o = 0 := by
  unfold missing
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro a ha; simp [h a ha]

theorem missing_single_pos {s : sym} {o : List sym} (h : Lem_List.elem s o = false) :
    1 ≤ missing [s] o := by
  unfold missing; simp [h]

theorem hops_cons_le (t1 t2 : Table) (q : sym × sym) (A : List (sym × sym)) :
    hops t1 t2 (q :: A) ≤ hops t1 t2 A := by
  unfold hops
  apply List.Sublist.length_le
  apply filter_sublist_of_imp
  intro x hx
  rw [Bool.not_eq_true'] at hx ⊢
  exact not_elem_of_not_elem_cons hx

/-! ## Symbol equality: an equivalence relation on (digest, number) -/

theorem digest_compare_eq_zero_iff (x y : String) :
    (CerberusFresh.digest_compare x y == (0 : Int)) = true ↔ x = y := by
  unfold CerberusFresh.digest_compare
  constructor
  · intro h
    split at h
    · simp at h
    · split at h
      · rename_i _ hxy; exact eq_of_beq hxy
      · simp at h
  · rintro rfl
    simp [String.lt_irrefl]

/-- The `Eq0 Nat` instance the symbol instance uses for the number (LemLib's
    `instEq0Nat_1`, whose `isEqual` is core's `==` on `Nat` since the BEq
    lattice moved the `[Eq0 a] : BEq a` bridge below core's instance,
    lem-lean 2026-10-03; before that it bottomed out in `defaultCompare`). -/
theorem natEq0_iff (n1 n2 : Nat) : Lem_Basic_classes.isEqual n1 n2 = true ↔ n1 = n2 := by
  show (n1 == n2) = true ↔ n1 = n2
  exact beq_iff_eq

/-- The model's `Eq0 sym` instance (symbol.lem `symbolEqual`) is digest equality and
    number equality; the description is ignored. -/
theorem symEq_iff (a b : sym) :
    Lem_Basic_classes.isEqual a b = true ↔
      digest_of_sym a = digest_of_sym b ∧ symbol_num a = symbol_num b := by
  obtain ⟨d1, n1, sd1⟩ := a
  obtain ⟨d2, n2, sd2⟩ := b
  simp only [digest_of_sym, symbol_num]
  show (if (CerberusFresh.digest_compare d1 d2 == (0 : Int) && n1 == n2) = true then
      (if (natGteb 0 5 && sd1 != sd2) = true then true else true) else false) = true ↔ _
  rw [ite_self]
  constructor
  · intro h
    split at h
    · rename_i hc
      rw [Bool.and_eq_true] at hc
      exact ⟨(digest_compare_eq_zero_iff d1 d2).mp hc.1, (natEq0_iff n1 n2).mp hc.2⟩
    · exact absurd h Bool.false_ne_true
  · rintro ⟨rfl, rfl⟩
    have hc : (CerberusFresh.digest_compare d1 d1 == (0 : Int) && (n1 == n1)) = true := by
      rw [Bool.and_eq_true]
      exact ⟨(digest_compare_eq_zero_iff d1 d1).mpr rfl, (natEq0_iff n1 n1).mpr rfl⟩
    rw [if_pos hc]

theorem symEq_refl (a : sym) : Lem_Basic_classes.isEqual a a = true :=
  (symEq_iff a a).mpr ⟨rfl, rfl⟩

theorem symEq_symm {a b : sym} (h : Lem_Basic_classes.isEqual a b = true) :
    Lem_Basic_classes.isEqual b a = true := by
  rw [symEq_iff] at h ⊢; exact ⟨h.1.symm, h.2.symm⟩

theorem symEq_trans {a b c : sym} (h1 : Lem_Basic_classes.isEqual a b = true)
    (h2 : Lem_Basic_classes.isEqual b c = true) : Lem_Basic_classes.isEqual a c = true := by
  rw [symEq_iff] at h1 h2 ⊢; exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- The `Eq0` product instance: componentwise. -/
theorem pairEq_iff (a b c d : sym) :
    Lem_Basic_classes.isEqual (a, b) (c, d) = true ↔
      Lem_Basic_classes.isEqual a c = true ∧ Lem_Basic_classes.isEqual b d = true := by
  show (Lem_Basic_classes.isEqual a c && Lem_Basic_classes.isEqual b d) = true ↔ _
  exact Iff.of_eq (Bool.and_eq_true _ _)

theorem mem_elem_sym {a : sym} {l : List sym} (h : a ∈ l) : Lem_List.elem a l = true :=
  (elem_true_iff a l).mpr ⟨a, h, symEq_refl a⟩

/-! ## Pairs -/

theorem mem_pairs {a b : sym} {l1 l2 : List sym} (ha : a ∈ l1) (hb : b ∈ l2) :
    (a, b) ∈ pairs l1 l2 := by
  unfold pairs
  rw [List.mem_flatMap]
  exact ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩

/-- The hop that consumes a pair: both tags occur in the tables and the pair was not
    assumed, so strictly fewer pairs remain. -/
theorem hops_cons_lt {t1 t2 : Table} {A : List (sym × sym)} {s1 s2 : sym}
    (h1 : Lem_List.elem s1 (occ t1) = true) (h2 : Lem_List.elem s2 (occ t2) = true)
    (hA : Lem_List.elem (s1, s2) A = false) :
    hops t1 t2 ((s1, s2) :: A) < hops t1 t2 A := by
  unfold hops
  obtain ⟨a, ha, hsa⟩ := (elem_true_iff s1 (occ t1)).mp h1
  obtain ⟨b, hb, hsb⟩ := (elem_true_iff s2 (occ t2)).mp h2
  apply filter_length_lt_of_imp
  · intro x hx
    rw [Bool.not_eq_true'] at hx ⊢
    exact not_elem_of_not_elem_cons hx
  · refine ⟨(a, b), mem_pairs ha hb, ?_, ?_⟩
    · -- (a, b) is not assumed: otherwise (s1, s2) would be, by transitivity
      rw [Bool.not_eq_true']
      cases h : Lem_List.elem (a, b) A with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨⟨c, d⟩, hcd, hab⟩ := (elem_true_iff (a, b) A).mp h
        rw [pairEq_iff] at hab
        have : Lem_List.elem (s1, s2) A = true :=
          (elem_true_iff (s1, s2) A).mpr ⟨(c, d), hcd,
            (pairEq_iff s1 s2 c d).mpr ⟨symEq_trans hsa hab.1, symEq_trans hsb hab.2⟩⟩
        rw [this] at hA; exact Bool.noConfusion hA
    · -- (a, b) is assumed once (s1, s2) is: it is `==` to the head
      rw [elem_cons, (pairEq_iff a b s1 s2).mpr ⟨symEq_symm hsa, symEq_symm hsb⟩]
      rfl

/-! ## Lookups: a found value is one of the tree's nodes -/

theorem find?_some_bounds {cmp : sym → sym → LemOrdering} {k : sym}
    {m : Pmap sym (CerbLocation.Loc × tag_definition)} {v : CerbLocation.Loc × tag_definition}
    (h : Pmap.find? cmp k m = some v) :
    defSize v.2 ≤ pmapValsSize m ∧ (defTags v.2).Sublist (pmapTags m) := by
  induction m with
  | Empty => simp [Pmap.find?] at h
  | Node l key d r n ihl ihr =>
    obtain ⟨loc, dd⟩ := d
    simp only [Pmap.find?] at h
    split at h
    · -- EQ: the node itself
      cases h
      refine ⟨?_, ?_⟩
      · simp only [pmapValsSize]; omega
      · simp only [pmapTags]
        exact (List.sublist_append_right (pmapTags l) (defTags dd)).trans
          (List.sublist_append_left _ (pmapTags r))
    · -- LT: the left subtree
      obtain ⟨h1, h2⟩ := ihl h
      refine ⟨?_, ?_⟩
      · simp only [pmapValsSize]; omega
      · simp only [pmapTags]
        exact (h2.trans (List.sublist_append_left (pmapTags l) (defTags dd))).trans
          (List.sublist_append_left _ (pmapTags r))
    · -- GT: the right subtree
      obtain ⟨h1, h2⟩ := ihr h
      refine ⟨?_, ?_⟩
      · simp only [pmapValsSize]; omega
      · simp only [pmapTags]
        exact h2.trans (List.sublist_append_right _ (pmapTags r))

theorem fmapLookupBy_some_bounds {cmp : sym → sym → LemOrdering} {k : sym} {t : Table}
    {v : CerbLocation.Loc × tag_definition} (h : fmapLookupBy cmp k t = some v) :
    defSize v.2 ≤ valsSize t ∧ (defTags v.2).Sublist (occ t) := by
  cases t with
  | empty => simp [fmapLookupBy] at h
  | mk c m => exact find?_some_bounds (m := m) h

/-! ## Members: size and tags of a member type -/

theorem member_size_le {u : ctype} {i : identifier} {at_ : attributes} {al : Option alignment}
    {q : qualifiers} {xs : List Member} (h : (i, (at_, al, q, u)) ∈ xs) :
    ctype.lemSize u ≤ memberSizes xs := by
  induction xs with
  | nil => exact absurd h List.not_mem_nil
  | cons y ys ih =>
    obtain ⟨i', at', al', q', u'⟩ := y
    simp only [memberSizes]
    rcases List.mem_cons.mp h with heq | h'
    · cases heq; omega
    · have := ih h'; omega

theorem member_tags_sublist {u : ctype} {i : identifier} {at_ : attributes} {al : Option alignment}
    {q : qualifiers} {xs : List Member} (h : (i, (at_, al, q, u)) ∈ xs) :
    (tagsIn u).Sublist (memberTags xs) := by
  induction xs with
  | nil => exact absurd h List.not_mem_nil
  | cons y ys ih =>
    obtain ⟨i', at', al', q', u'⟩ := y
    simp only [memberTags]
    rcases List.mem_cons.mp h with heq | h'
    · cases heq; exact List.sublist_append_left _ _
    · exact (ih h').trans (List.sublist_append_right _ _)

/-- A struct member's contribution: its size is at most the table's, and its tags all
    occur in the table (so its `missing` count is 0). -/
theorem member_bounds {cmp : sym → sym → LemOrdering} {s : sym} {t : Table}
    {loc : CerbLocation.Loc} {xs : List Member} {fo : Option flexible_array_member}
    (hl : fmapLookupBy cmp s t = some (loc, .StructDef xs fo))
    {u : ctype} {i : identifier} {at_ : attributes} {al : Option alignment} {q : qualifiers}
    (hm : (i, (at_, al, q, u)) ∈ xs) :
    ctype.lemSize u ≤ valsSize t ∧ missing (tagsIn u) (occ t) = 0 := by
  obtain ⟨hs, ht⟩ := fmapLookupBy_some_bounds hl
  simp only [defSize, defTags] at hs ht
  refine ⟨?_, ?_⟩
  · have := member_size_le hm; omega
  · apply missing_eq_zero
    intro a ha
    apply mem_elem_sym
    exact ht.subset (List.mem_append_left _ ((member_tags_sublist hm).subset ha))

theorem union_member_bounds {cmp : sym → sym → LemOrdering} {s : sym} {t : Table}
    {loc : CerbLocation.Loc} {xs : List Member}
    (hl : fmapLookupBy cmp s t = some (loc, .UnionDef xs))
    {u : ctype} {i : identifier} {at_ : attributes} {al : Option alignment} {q : qualifiers}
    (hm : (i, (at_, al, q, u)) ∈ xs) :
    ctype.lemSize u ≤ valsSize t ∧ missing (tagsIn u) (occ t) = 0 := by
  obtain ⟨hs, ht⟩ := fmapLookupBy_some_bounds hl
  simp only [defSize, defTags] at hs ht
  refine ⟨?_, ?_⟩
  · have := member_size_le hm; omega
  · apply missing_eq_zero
    intro a ha
    apply mem_elem_sym
    exact ht.subset ((member_tags_sublist hm).subset ha)

theorem flex_bounds {cmp : sym → sym → LemOrdering} {s : sym} {t : Table}
    {loc : CerbLocation.Loc} {xs : List Member} {at_ : attributes} {i : identifier}
    {q : qualifiers} {u : ctype}
    (hl : fmapLookupBy cmp s t = some (loc, .StructDef xs (some (.FlexibleArrayMember at_ i q u)))) :
    ctype.lemSize u ≤ valsSize t ∧ missing (tagsIn u) (occ t) = 0 := by
  obtain ⟨hs, ht⟩ := fmapLookupBy_some_bounds hl
  simp only [defSize, defTags, flexSize, flexTags] at hs ht
  refine ⟨by omega, ?_⟩
  apply missing_eq_zero
  intro a ha
  apply mem_elem_sym
  exact ht.subset (List.mem_append_right _ ha)

/-! ## The decrease lemmas the stability proof uses -/

/-- Structural step: the children's tags are sublists of the parents' and both sizes
    strictly shrink. -/
theorem auxGeneral_lt_of_structural {t1 t2 : Table} {A : List (sym × sym)}
    {q1 q2 qs1 qs2 : qualifiers} {u1 u2 v1 v2 : ctype}
    (ht1 : (tagsIn u1).Sublist (tagsIn v1)) (ht2 : (tagsIn u2).Sublist (tagsIn v2))
    (hs1 : ctype.lemSize u1 < ctype.lemSize v1) (hs2 : ctype.lemSize u2 < ctype.lemSize v2) :
    auxGeneral (t1, t2, A) (q1, u1) (q2, u2) < auxGeneral (t1, t2, A) (qs1, v1) (qs2, v2) := by
  simp only [auxGeneral, count]
  have m1 := missing_sublist (o := occ t1) ht1
  have m2 := missing_sublist (o := occ t2) ht2
  have := Nat.mul_le_mul_right (weight t1 t2)
    (Nat.add_le_add (Nat.add_le_add (Nat.le_refl (hops t1 t2 A)) m1) m2)
  omega

/-- The hop: both children are member types looked up in the tables, the pair was not
    assumed. -/
theorem auxGeneral_lt_of_hop {t1 t2 : Table} {A : List (sym × sym)} {s1 s2 : sym}
    {q1 q2 qs1 qs2 : qualifiers} {u1 u2 : ctype} {a1 a2 : List annot}
    {ty1 ty2 : ctype_}
    (hty1 : tagsIn_ ty1 = [s1]) (hty2 : tagsIn_ ty2 = [s2])
    (hA : Lem_List.elem (s1, s2) A = false)
    (hu1 : ctype.lemSize u1 ≤ valsSize t1 ∧ missing (tagsIn u1) (occ t1) = 0)
    (hu2 : ctype.lemSize u2 ≤ valsSize t2 ∧ missing (tagsIn u2) (occ t2) = 0) :
    auxGeneral (t1, t2, (s1, s2) :: A) (q1, u1) (q2, u2)
      < auxGeneral (t1, t2, A) (qs1, .Ctype a1 ty1) (qs2, .Ctype a2 ty2) := by
  simp only [auxGeneral, count, tagsIn, hty1, hty2, hu1.2, hu2.2, Nat.add_zero]
  -- count' + 1 ≤ count
  have hc : hops t1 t2 ((s1, s2) :: A) + 1 ≤
      hops t1 t2 A + missing [s1] (occ t1) + missing [s2] (occ t2) := by
    cases h1 : Lem_List.elem s1 (occ t1) with
    | false => have := missing_single_pos h1; have := hops_cons_le t1 t2 (s1, s2) A; omega
    | true =>
      cases h2 : Lem_List.elem s2 (occ t2) with
      | false => have := missing_single_pos h2; have := hops_cons_le t1 t2 (s1, s2) A; omega
      | true => have := hops_cons_lt h1 h2 hA; omega
  have hw := Nat.mul_le_mul_right (weight t1 t2) hc
  rw [Nat.succ_mul] at hw
  have hW : weight t1 t2 = valsSize t1 + valsSize t2 + 1 := rfl
  omega

/-! ## The decrease at each recursive call site of the generated block, packaged -/

theorem size_ctype (a : List annot) (t : ctype_) :
    ctype.lemSize (.Ctype a t) = 1 + ctype_.lemSize t := rfl

/-- `Array0` arm: the element types. -/
theorem lt_array {t1 t2 : Table} {A : List (sym × sym)} {q1 q2 qs1 qs2 : qualifiers}
    {e1 e2 : ctype} {a1 a2 : List annot} {n1 n2 : Option Int} :
    auxGeneral (t1, t2, A) (q1, e1) (q2, e2)
      < auxGeneral (t1, t2, A) (qs1, .Ctype a1 (.Array0 e1 n1)) (qs2, .Ctype a2 (.Array0 e2 n2)) :=
  auxGeneral_lt_of_structural (List.Sublist.refl _) (List.Sublist.refl _)
    (by simp only [size_ctype, ctype_.lemSize]; omega)
    (by simp only [size_ctype, ctype_.lemSize]; omega)

/-- `Pointer` arm: the referenced types. -/
theorem lt_pointer {t1 t2 : Table} {A : List (sym × sym)} {q1 q2 qs1 qs2 rq1 rq2 : qualifiers}
    {e1 e2 : ctype} {a1 a2 : List annot} :
    auxGeneral (t1, t2, A) (q1, e1) (q2, e2)
      < auxGeneral (t1, t2, A) (qs1, .Ctype a1 (.Pointer rq1 e1)) (qs2, .Ctype a2 (.Pointer rq2 e2)) :=
  auxGeneral_lt_of_structural (List.Sublist.refl _) (List.Sublist.refl _)
    (by simp only [size_ctype, ctype_.lemSize]; omega)
    (by simp only [size_ctype, ctype_.lemSize]; omega)

/-- `Atomic` arm: the atomic types. -/
theorem lt_atomic {t1 t2 : Table} {A : List (sym × sym)} {q1 q2 qs1 qs2 : qualifiers}
    {e1 e2 : ctype} {a1 a2 : List annot} :
    auxGeneral (t1, t2, A) (q1, e1) (q2, e2)
      < auxGeneral (t1, t2, A) (qs1, .Ctype a1 (.Atomic e1)) (qs2, .Ctype a2 (.Atomic e2)) :=
  auxGeneral_lt_of_structural (List.Sublist.refl _) (List.Sublist.refl _)
    (by simp only [size_ctype, ctype_.lemSize]; omega)
    (by simp only [size_ctype, ctype_.lemSize]; omega)

/-- `Function` arm, the return types. -/
theorem lt_function_ret {t1 t2 : Table} {A : List (sym × sym)} {q1 q2 qs1 qs2 rq1 rq2 : qualifiers}
    {r1 r2 : ctype} {a1 a2 : List annot} {ps1 ps2 : List Param} {v1 v2 : Bool} :
    auxGeneral (t1, t2, A) (q1, r1) (q2, r2)
      < auxGeneral (t1, t2, A) (qs1, .Ctype a1 (.Function (rq1, r1) ps1 v1))
          (qs2, .Ctype a2 (.Function (rq2, r2) ps2 v2)) :=
  auxGeneral_lt_of_structural (List.sublist_append_left _ _) (List.sublist_append_left _ _)
    (by simp only [size_ctype, ctype_.lemSize]; omega)
    (by simp only [size_ctype, ctype_.lemSize]; omega)

/-- `Function` arm, the parameter lists (the `are_compatible_params` call). -/
theorem lt_function_params {t1 t2 : Table} {A : List (sym × sym)} {qs1 qs2 rq1 rq2 : qualifiers}
    {r1 r2 : ctype} {a1 a2 : List annot} {ps1 ps2 : List Param} {v1 v2 : Bool} :
    paramsBound (t1, t2, A) ps1 ps2
      < auxGeneral (t1, t2, A) (qs1, .Ctype a1 (.Function (rq1, r1) ps1 v1))
          (qs2, .Ctype a2 (.Function (rq2, r2) ps2 v2)) := by
  simp only [paramsBound, paramsAuxBound, auxGeneral, count, tagsIn, tagsIn_, size_ctype,
    ctype_.lemSize]
  have m1 := missing_sublist (o := occ t1) (List.sublist_append_right (tagsIn r1) (tagsInParams ps1))
  have m2 := missing_sublist (o := occ t2) (List.sublist_append_right (tagsIn r2) (tagsInParams ps2))
  have := Nat.mul_le_mul_right (weight t1 t2)
    (Nat.add_le_add (Nat.add_le_add (Nat.le_refl (hops t1 t2 A)) m1) m2)
  have := ctype_lemSize_pos r1
  have := ctype_lemSize_pos r2
  omega

/-- `are_compatible_params_aux`, the head types (the `are_compatible_aux` call). -/
theorem lt_params_head {t1 t2 : Table} {A : List (sym × sym)} {q1 q2 q1' q2' : qualifiers}
    {u1 u2 : ctype} {b1 b2 : Bool} {ps1 ps2 : List Param} :
    auxGeneral (t1, t2, A) (q1, u1) (q2, u2)
      < paramsAuxBound (t1, t2, A) ((q1', u1, b1) :: ps1, (q2', u2, b2) :: ps2) := by
  simp only [paramsAuxBound, auxGeneral, count, tagsInParams, ctype_.lemSize_aux1]
  have m1 := missing_sublist (o := occ t1) (List.sublist_append_left (tagsIn u1) (tagsInParams ps1))
  have m2 := missing_sublist (o := occ t2) (List.sublist_append_left (tagsIn u2) (tagsInParams ps2))
  have := Nat.mul_le_mul_right (weight t1 t2)
    (Nat.add_le_add (Nat.add_le_add (Nat.le_refl (hops t1 t2 A)) m1) m2)
  omega

/-- `are_compatible_params_aux`, the tails. -/
theorem lt_params_tail {t1 t2 : Table} {A : List (sym × sym)} {q1' q2' : qualifiers}
    {u1 u2 : ctype} {b1 b2 : Bool} {ps1 ps2 : List Param} :
    paramsAuxBound (t1, t2, A) (ps1, ps2)
      < paramsAuxBound (t1, t2, A) ((q1', u1, b1) :: ps1, (q2', u2, b2) :: ps2) := by
  simp only [paramsAuxBound, count, tagsInParams, ctype_.lemSize_aux1]
  have m1 := missing_sublist (o := occ t1) (List.sublist_append_right (tagsIn u1) (tagsInParams ps1))
  have m2 := missing_sublist (o := occ t2) (List.sublist_append_right (tagsIn u2) (tagsInParams ps2))
  have := Nat.mul_le_mul_right (weight t1 t2)
    (Nat.add_le_add (Nat.add_le_add (Nat.le_refl (hops t1 t2 A)) m1) m2)
  have := ctype_lemSize_pos u1
  omega

/-- `are_compatible_params` calls the aux at fuel − 1 on the same lists. -/
theorem lt_params {env1 : Env} {ps1 ps2 : List Param} :
    paramsAuxBound env1 (ps1, ps2) < paramsBound env1 ps1 ps2 := by
  unfold paramsBound; omega

/-- Membership-relative congruence for `List.all` (the recursive call sits under the
    traversal's lambda; its bound needs the element's membership). -/
theorem all_congr {α : Type} (l : List α) (F G : α → Bool) (h : ∀ x, x ∈ l → F x = G x) :
    l.all F = l.all G := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-! ## Entry fuels

The three measures above are what the proofs need: every cross-call of the block
strictly decreases them. They are also what the generated wrappers used to pass as
the block's starting fuel, and `hops` materializes every pair of tag occurrences of
the two tables, so each `are_compatible*` call cost time quadratic in the tables
(about 23% of a linked X25519 run, plus the allocation of those pairs).

A wrapper may start the block at ANY fuel at or above its measure: the
`*_measure_sufficient` obligations (Ctype_aux_lemMeasureProofs) show the worker is
stable there. The entry fuels below replace `hops` by its A-independent upper bound
`|occ t1| * |occ t2|` (two list lengths, no pair list). Every result is unchanged;
the only difference is a larger starting fuel, which the block never exhausts. -/

/-- An upper bound of `hops t1 t2 A` for every `A`. -/
def hopsFuel (t1 t2 : Table) : Nat := (occ t1).length * (occ t2).length

def countFuel (t1 t2 : Table) (tags1 tags2 : List sym) : Nat :=
  hopsFuel t1 t2 + missing tags1 (occ t1) + missing tags2 (occ t2)

/-- Entry fuel of `are_compatible_aux` (the `fuel_measure` declare in ctype_aux.lem). -/
def auxFuel (p : Env) (p0 p1 : qualifiers × ctype) : Nat :=
  if sameTuTags p0.2 p1.2 then 1 else
  match p with
  | (t1, t2, _) =>
    countFuel t1 t2 (tagsIn p0.2) (tagsIn p1.2) * weight t1 t2
      + ctype.lemSize p0.2 + ctype.lemSize p1.2 + 1

/-- Entry fuel of `are_compatible_params_aux`. -/
def paramsAuxFuel (env1 : Env) (lemTail : List Param × List Param) : Nat :=
  match env1 with
  | (t1, t2, _) =>
    countFuel t1 t2 (tagsInParams lemTail.1) (tagsInParams lemTail.2) * weight t1 t2
      + ctype_.lemSize_aux1 lemTail.1 + ctype_.lemSize_aux1 lemTail.2 + 1

/-- Entry fuel of `are_compatible_params`. -/
def paramsFuel (env1 : Env) (params1 params2 : List Param) : Nat :=
  paramsAuxFuel env1 (params1, params2) + 1

theorem length_pairs (l1 l2 : List sym) : (pairs l1 l2).length = l1.length * l2.length := by
  induction l1 with
  | nil => simp [pairs]
  | cons a l ih =>
    simp only [pairs, List.flatMap_cons, List.length_append, List.length_map, List.length_cons] at ih ⊢
    rw [ih, Nat.succ_mul]; omega

theorem hops_le_hopsFuel (t1 t2 : Table) (A : List (sym × sym)) : hops t1 t2 A ≤ hopsFuel t1 t2 := by
  unfold hops hopsFuel
  rw [← length_pairs]
  exact List.length_filter_le _ _

theorem count_le_countFuel (t1 t2 : Table) (A : List (sym × sym)) (tags1 tags2 : List sym) :
    count t1 t2 A tags1 tags2 ≤ countFuel t1 t2 tags1 tags2 := by
  unfold count countFuel; have := hops_le_hopsFuel t1 t2 A; omega

theorem auxBound_le_auxFuel (p : Env) (p0 p1 : qualifiers × ctype) :
    auxBound p p0 p1 ≤ auxFuel p p0 p1 := by
  obtain ⟨t1, t2, A⟩ := p
  unfold auxBound auxFuel; split
  · exact Nat.le_refl 1
  · simp only [auxGeneral]
    have := Nat.mul_le_mul_right (weight t1 t2)
      (count_le_countFuel t1 t2 A (tagsIn p0.2) (tagsIn p1.2))
    omega

theorem paramsAuxBound_le_paramsAuxFuel (env1 : Env) (lemTail : List Param × List Param) :
    paramsAuxBound env1 lemTail ≤ paramsAuxFuel env1 lemTail := by
  obtain ⟨t1, t2, A⟩ := env1
  simp only [paramsAuxBound, paramsAuxFuel]
  have := Nat.mul_le_mul_right (weight t1 t2)
    (count_le_countFuel t1 t2 A (tagsInParams lemTail.1) (tagsInParams lemTail.2))
  omega

theorem paramsBound_le_paramsFuel (env1 : Env) (params1 params2 : List Param) :
    paramsBound env1 params1 params2 ≤ paramsFuel env1 params1 params2 := by
  unfold paramsBound paramsFuel
  have := paramsAuxBound_le_paramsAuxFuel env1 (params1, params2); omega

end CerbCtypeMeasure
