/-
  Ctype_aux_lemMeasureProofs — the hand-written proofs of the three `fuel_measure`
  obligations lem emits into Ctype_aux_auxiliary.lean for the `are_compatible_aux`
  mutual block (are-compatible-assumed-set slice, 2026-09-10; Lean-only declares in
  frontend/model/ctype_aux.lem):

    are_compatible_aux         = `CerbCtypeMeasure.auxFuel p p0 p1`
    are_compatible_params_aux  = `CerbCtypeMeasure.paramsAuxFuel env1 lemTail`
    are_compatible_params      = `CerbCtypeMeasure.paramsFuel env1 params1 params2`

  These entry fuels are at or above the measures auxBound/paramsAuxBound/paramsBound
  (CerbCtypeMeasure's `*_le_*Fuel` lemmas); the stability lemma is stated over the
  measures, and each obligation applies it to the entry fuel and the caller's fuel.

  The block shares ONE fuel counter (lem demutualizes a mutual block over a single
  `lemFuel`, decremented at every hop), so each member's measure bounds the WHOLE
  block's call depth from that entry: every cross-call strictly decreases the callee's
  measure (CerbCtypeMeasure's `lt_*` lemmas). The measures are hypothesis-free.

  Shape: the C2/C3 template — one joint stability statement for the three members by
  induction on a bound k (any two fuels at or above the measure agree), each worker
  unfolded one step, every recursive call rewritten by a `key` whose side condition is
  the corresponding decrease lemma. The two hop arms (cross-TU Struct/Struct and
  Union/Union) descend under the member traversal's lambda with `all_congr`, which
  supplies the member's membership and hence its bounds (`member_bounds`,
  `union_member_bounds`, `flex_bounds`). Kernel-only tactics; no option bumps.

  MIRROR-OCAML NOTE: proofs about the Lean total workers; no OCaml text corresponds
  (fuel is a Lean-target artifact).
-/

import Ctype_aux
import CerbCtypeMeasure
import LemLibTheorems

set_option autoImplicit false

namespace Ctype_aux_lemMeasureProofs

open CerbCtypeMeasure

/-- The joint stability lemma for the mutual block: above each member's measure, any
    two fuels agree. -/
theorem stable_aux (enumDefs : Fmap sym integerType) (tagDefs : Fmap sym (CerbLocation.Loc × tag_definition)) (k : Nat) :
    (∀ (t1 t2 : Table) (A : List (sym × sym)) (qs1 qs2 : qualifiers) (ty1 ty2 : ctype) (f g : Nat),
      auxBound (t1, t2, A) (qs1, ty1) (qs2, ty2) ≤ k →
      auxBound (t1, t2, A) (qs1, ty1) (qs2, ty2) ≤ f →
      auxBound (t1, t2, A) (qs1, ty1) (qs2, ty2) ≤ g →
      are_compatible_aux_lemFuel f enumDefs tagDefs (t1, t2, A) (qs1, ty1) (qs2, ty2) =
        are_compatible_aux_lemFuel g enumDefs tagDefs (t1, t2, A) (qs1, ty1) (qs2, ty2)) ∧
    (∀ (t1 t2 : Table) (A : List (sym × sym)) (acc : Bool) (l1 l2 : List Param) (f g : Nat),
      paramsAuxBound (t1, t2, A) (l1, l2) ≤ k →
      paramsAuxBound (t1, t2, A) (l1, l2) ≤ f →
      paramsAuxBound (t1, t2, A) (l1, l2) ≤ g →
      are_compatible_params_aux0_lemFuel f enumDefs tagDefs (t1, t2, A) acc (l1, l2) =
        are_compatible_params_aux0_lemFuel g enumDefs tagDefs (t1, t2, A) acc (l1, l2)) ∧
    (∀ (t1 t2 : Table) (A : List (sym × sym)) (ps1 ps2 : List Param) (f g : Nat),
      paramsBound (t1, t2, A) ps1 ps2 ≤ k →
      paramsBound (t1, t2, A) ps1 ps2 ≤ f →
      paramsBound (t1, t2, A) ps1 ps2 ≤ g →
      are_compatible_params0_lemFuel f enumDefs tagDefs (t1, t2, A) ps1 ps2 =
        are_compatible_params0_lemFuel g enumDefs tagDefs (t1, t2, A) ps1 ps2) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro t1 t2 A qs1 qs2 ty1 ty2 f g hk _ _
      have := auxBound_pos (t1, t2, A) (qs1, ty1) (qs2, ty2); omega
    · intro t1 t2 A acc l1 l2 f g hk _ _
      have := paramsAuxBound_pos (t1, t2, A) (l1, l2); omega
    · intro t1 t2 A ps1 ps2 f g hk _ _
      have := paramsBound_pos (t1, t2, A) ps1 ps2; omega
  | succ k ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    -- ===== are_compatible_aux enumDefs tagDefs =====
    · intro t1 t2 A qs1 qs2 ty1 ty2 f g hk hf hg
      have hpos := auxBound_pos (t1, t2, A) (qs1, ty1) (qs2, ty2)
      cases f with
      | zero => omega
      | succ f =>
      cases g with
      | zero => omega
      | succ g =>
      -- a recursive call whose GENERAL bound is below this entry's bound agrees
      have key : ∀ (A' : List (sym × sym)) (q1 : qualifiers) (u1 : ctype) (q2 : qualifiers)
          (u2 : ctype),
          auxGeneral (t1, t2, A') (q1, u1) (q2, u2) < auxBound (t1, t2, A) (qs1, ty1) (qs2, ty2) →
          are_compatible_aux_lemFuel f enumDefs tagDefs (t1, t2, A') (q1, u1) (q2, u2) =
            are_compatible_aux_lemFuel g enumDefs tagDefs (t1, t2, A') (q1, u1) (q2, u2) := by
        intro A' q1 u1 q2 u2 h
        have := auxBound_le_general (t1, t2, A') (q1, u1) (q2, u2)
        exact ih1 t1 t2 A' q1 q2 u1 u2 f g (by omega) (by omega) (by omega)
      have keyP : ∀ (ps1 ps2 : List Param),
          paramsBound (t1, t2, A) ps1 ps2 < auxBound (t1, t2, A) (qs1, ty1) (qs2, ty2) →
          are_compatible_params0_lemFuel f enumDefs tagDefs (t1, t2, A) ps1 ps2 =
            are_compatible_params0_lemFuel g enumDefs tagDefs (t1, t2, A) ps1 ps2 := by
        intro ps1 ps2 h
        exact ih3 t1 t2 A ps1 ps2 f g (by omega) (by omega) (by omega)
      obtain ⟨a1, ty1⟩ := ty1
      obtain ⟨a2, ty2⟩ := ty2
      simp only [are_compatible_aux_lemFuel]
      cases hq : qualifiersEqual qs1 qs2
      · rfl
      simp only [Bool.true_and]
      cases ty1 <;> cases ty2 <;> try simp only [] <;> try rfl
      -- Array0: the element types
      case Array0.Array0 e1 n1 e2 n2 =>
        rw [key A no_qualifiers e1 no_qualifiers e2 (by rw [auxBound_eq_general rfl]; exact lt_array)]
      -- Function: the return types, then the parameter lists
      case Function.Function p1 ps1 v1 p2 ps2 v2 =>
        obtain ⟨rq1, r1⟩ := p1
        obtain ⟨rq2, r2⟩ := p2
        simp only []
        rw [key A rq1 r1 rq2 r2 (by rw [auxBound_eq_general rfl]; exact lt_function_ret),
          keyP ps1 ps2 (by rw [auxBound_eq_general rfl]; exact lt_function_params)]
      -- Pointer: the referenced types
      case Pointer.Pointer rq1 e1 rq2 e2 =>
        rw [key A rq1 e1 rq2 e2 (by rw [auxBound_eq_general rfl]; exact lt_pointer)]
      -- Atomic
      case Atomic.Atomic e1 e2 =>
        rw [key A no_qualifiers e1 no_qualifiers e2 (by rw [auxBound_eq_general rfl]; exact lt_atomic)]
      -- Struct/Struct: the hop. After the same-TU test comes `tags_correspond` (equal
      -- `SD_Id` names, or two unnamed tags); nothing below names the tags.
      case Struct.Struct s1 s2 =>
        split
        · rfl
        next hsame =>
        have hgen : auxBound (t1, t2, A) (qs1, .Ctype a1 (.Struct s1)) (qs2, .Ctype a2 (.Struct s2)) =
            auxGeneral (t1, t2, A) (qs1, .Ctype a1 (.Struct s1)) (qs2, .Ctype a2 (.Struct s2)) :=
          auxBound_eq_general (Bool.of_not_eq_true hsame)
        -- `if tags_correspond tag1 tag2` (else: `false = false`)
        split <;> try rfl
        -- `if elem (tag1, tag2) assumed` (then: `true = true`)
        all_goals split <;> try rfl
        all_goals
          rename_i hA
          have hA' := Bool.of_not_eq_true hA
          -- the lookups: only the StructDef/StructDef arm recurses
          split <;> try rfl
          rename_i _ xs1 fo1 _ xs2 fo2 hl1 hl2
          -- `if not (length == length)` (then: `false = false`)
          split <;> try rfl
          congr 1
          · apply all_congr
            intro q hq
            obtain ⟨⟨i1, at1, al1, q1, u1⟩, ⟨i2, at2, al2, q2, u2⟩⟩ := q
            rw [LemLibTheorems.lemListZip_eq] at hq
            have hm := List.of_mem_zip hq
            try simp only []
            rw [key _ q1 u1 q2 u2 (by
              rw [hgen]
              exact auxGeneral_lt_of_hop rfl rfl hA' (member_bounds hl1 hm.1) (member_bounds hl2 hm.2))]
          · split <;> try rfl
            rename_i _ i1 q1 u1 _ i2 q2 u2
            rw [key _ q1 u1 q2 u2 (by
              rw [hgen]
              exact auxGeneral_lt_of_hop rfl rfl hA' (flex_bounds hl1) (flex_bounds hl2))]
      -- Union0/Union0: the hop (same shape, no flexible member)
      case Union0.Union0 s1 s2 =>
        split
        · rfl
        next hsame =>
        have hgen : auxBound (t1, t2, A) (qs1, .Ctype a1 (.Union0 s1)) (qs2, .Ctype a2 (.Union0 s2)) =
            auxGeneral (t1, t2, A) (qs1, .Ctype a1 (.Union0 s1)) (qs2, .Ctype a2 (.Union0 s2)) :=
          auxBound_eq_general (Bool.of_not_eq_true hsame)
        split <;> try rfl
        all_goals split <;> try rfl
        all_goals
          rename_i hA
          have hA' := Bool.of_not_eq_true hA
          split <;> try rfl
          rename_i _ xs1 _ xs2 hl1 hl2
          split <;> try rfl
          apply all_congr
          intro q hq
          obtain ⟨⟨i1, at1, al1, q1, u1⟩, ⟨i2, at2, al2, q2, u2⟩⟩ := q
          rw [LemLibTheorems.lemListZip_eq] at hq
          have hm := List.of_mem_zip hq
          try simp only []
          rw [key _ q1 u1 q2 u2 (by
            rw [hgen]
            exact auxGeneral_lt_of_hop rfl rfl hA' (union_member_bounds hl1 hm.1)
              (union_member_bounds hl2 hm.2))]
    -- ===== are_compatible_params_aux (the hoisted `lemTail` is the pair of lists) =====
    · intro t1 t2 A acc l1 l2 f g hk hf hg
      have hpos := paramsAuxBound_pos (t1, t2, A) (l1, l2)
      cases f with
      | zero => omega
      | succ f =>
      cases g with
      | zero => omega
      | succ g =>
      have key1 : ∀ (q1 : qualifiers) (u1 : ctype) (q2 : qualifiers) (u2 : ctype),
          auxGeneral (t1, t2, A) (q1, u1) (q2, u2) < paramsAuxBound (t1, t2, A) (l1, l2) →
          are_compatible_aux_lemFuel f enumDefs tagDefs (t1, t2, A) (q1, u1) (q2, u2) =
            are_compatible_aux_lemFuel g enumDefs tagDefs (t1, t2, A) (q1, u1) (q2, u2) := by
        intro q1 u1 q2 u2 h
        have := auxBound_le_general (t1, t2, A) (q1, u1) (q2, u2)
        exact ih1 t1 t2 A q1 q2 u1 u2 f g (by omega) (by omega) (by omega)
      have key2 : ∀ (acc' : Bool) (m1 m2 : List Param),
          paramsAuxBound (t1, t2, A) (m1, m2) < paramsAuxBound (t1, t2, A) (l1, l2) →
          are_compatible_params_aux0_lemFuel f enumDefs tagDefs (t1, t2, A) acc' (m1, m2) =
            are_compatible_params_aux0_lemFuel g enumDefs tagDefs (t1, t2, A) acc' (m1, m2) := by
        intro acc' m1 m2 h
        exact ih2 t1 t2 A acc' m1 m2 f g (by omega) (by omega) (by omega)
      rcases l1 with _ | ⟨⟨q1, u1, b1⟩, ps1⟩ <;> rcases l2 with _ | ⟨⟨q2, u2, b2⟩, ps2⟩ <;>
        simp only [are_compatible_params_aux0_lemFuel] <;> try rfl
      rw [key1 no_qualifiers u1 no_qualifiers u2 lt_params_head, key2 _ ps1 ps2 lt_params_tail]
    -- ===== are_compatible_params =====
    · intro t1 t2 A ps1 ps2 f g hk hf hg
      have hpos := paramsBound_pos (t1, t2, A) ps1 ps2
      cases f with
      | zero => omega
      | succ f =>
      cases g with
      | zero => omega
      | succ g =>
      simp only [are_compatible_params0_lemFuel]
      have := @lt_params (t1, t2, A) ps1 ps2
      exact ih2 t1 t2 A true ps1 ps2 f g (by omega) (by omega) (by omega)

/-- THE OBLIGATION, exactly as Ctype_aux_auxiliary.lean states and delegates it. The
    wrapper starts at `auxFuel`, which is at or above the measure `auxBound`; both
    fuels are above the measure, so `stable_aux` makes them agree. -/
theorem are_compatible_aux_measure_sufficient (enumDefs : Fmap sym integerType) (tagDefs : Fmap sym (CerbLocation.Loc × tag_definition)) (p : Env) (p0 p1 : qualifiers × ctype) (lemFuel : Nat)
    (lemMeasureLe : auxFuel p p0 p1 ≤ lemFuel) :
    are_compatible_aux_lemFuel lemFuel enumDefs tagDefs p p0 p1 = are_compatible_aux enumDefs tagDefs p p0 p1 := by
  obtain ⟨t1, t2, A⟩ := p
  obtain ⟨qs1, ty1⟩ := p0
  obtain ⟨qs2, ty2⟩ := p1
  have h := auxBound_le_auxFuel (t1, t2, A) (qs1, ty1) (qs2, ty2)
  exact (stable_aux enumDefs tagDefs (auxBound (t1, t2, A) (qs1, ty1) (qs2, ty2))).1 t1 t2 A qs1 qs2 ty1 ty2 lemFuel
    (auxFuel (t1, t2, A) (qs1, ty1) (qs2, ty2)) (Nat.le_refl _) (Nat.le_trans h lemMeasureLe) h

/-- THE OBLIGATION for the hoisted-tail member (`lemTail` = the pair of parameter lists). -/
theorem are_compatible_params_aux0_measure_sufficient (enumDefs : Fmap sym integerType) (tagDefs : Fmap sym (CerbLocation.Loc × tag_definition)) (env1 : Env) (acc : Bool)
    (lemTail : List Param × List Param) (lemFuel : Nat)
    (lemMeasureLe : paramsAuxFuel env1 lemTail ≤ lemFuel) :
    are_compatible_params_aux0_lemFuel lemFuel enumDefs tagDefs env1 acc lemTail =
      are_compatible_params_aux0 enumDefs tagDefs env1 acc lemTail := by
  obtain ⟨t1, t2, A⟩ := env1
  obtain ⟨l1, l2⟩ := lemTail
  have h := paramsAuxBound_le_paramsAuxFuel (t1, t2, A) (l1, l2)
  exact (stable_aux enumDefs tagDefs (paramsAuxBound (t1, t2, A) (l1, l2))).2.1 t1 t2 A acc l1 l2 lemFuel
    (paramsAuxFuel (t1, t2, A) (l1, l2)) (Nat.le_refl _) (Nat.le_trans h lemMeasureLe) h

/-- THE OBLIGATION, exactly as Ctype_aux_auxiliary.lean states and delegates it. -/
theorem are_compatible_params0_measure_sufficient (enumDefs : Fmap sym integerType) (tagDefs : Fmap sym (CerbLocation.Loc × tag_definition)) (env1 : Env) (params1 params2 : List Param)
    (lemFuel : Nat) (lemMeasureLe : paramsFuel env1 params1 params2 ≤ lemFuel) :
    are_compatible_params0_lemFuel lemFuel enumDefs tagDefs env1 params1 params2 =
      are_compatible_params0 enumDefs tagDefs env1 params1 params2 := by
  obtain ⟨t1, t2, A⟩ := env1
  have h := paramsBound_le_paramsFuel (t1, t2, A) params1 params2
  exact (stable_aux enumDefs tagDefs (paramsBound (t1, t2, A) params1 params2)).2.2 t1 t2 A params1 params2 lemFuel
    (paramsFuel (t1, t2, A) params1 params2) (Nat.le_refl _) (Nat.le_trans h lemMeasureLe) h

end Ctype_aux_lemMeasureProofs
