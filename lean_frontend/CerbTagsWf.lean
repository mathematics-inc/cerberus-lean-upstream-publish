/-
  CerbTagsWf — well-formedness of a tag environment (fuel-parameter arc C4,
  2026-09-05): the HYPOTHESIS vocabulary of the hypothesis-carrying measured
  seams (lem-lean `declare {lean} fuel_measure val f = `μ` assuming `H``,
  doc/lean-backend/2026-09-05_measure-hypothesis-record.md; the C2 record's
  D-C2-1, option 1 [USER 2026-09-05] "agree, go ahead with option 1").

  The layout oracle of CerbMem.lean (sizeof / alignof / offsetsof /
  offsetsofMembers / memberAlign, impl_mem.ml:98-273) and the byte
  deserializer (reconstructValue, impl_mem.ml:916-1095) recurse through TAG
  LOOKUPS: a struct/union type's size is computed from its members' types,
  read from the tag environment. No data measure over the parameters bounds
  that recursion — a cyclic table (`struct A { struct A a; }` written by
  hand into a Core file) makes it non-terminating — so the sufficiency
  obligation of a measured wrapper needs a hypothesis: the environment is
  ACYCLIC in the by-value sense, i.e. the "enters the definition of" relation
  on tags is well-founded (a RANK descends along every by-value reference).

  THE FRONTEND INVARIANT this rests on (the register scripts/fuel_hypotheses.txt
  cites it per row): a C translation unit's tag environment is acyclic by
  construction — frontend/model/cabs_to_ail.lem `check_members`
  (`:1512`, STD §6.7.2.1#3) refuses a struct/union member whose type is a
  function or INCOMPLETE; `AilTypesAux.is_complete` (frontend/model/ail/
  ailTypesAux.lem:222) makes a by-value `Struct sym`/`Union sym` complete only
  when `sym` is ALREADY in `sigm.tag_definitions`, an `Array` complete only when
  its element type is, `Atomic` when its inner type is, and a `Pointer`
  complete regardless of its target; the flexible array member's ELEMENT
  type is guaranteed by the Ail passes (`ailWf.lem:76-80`
  `ArrayDeclarationIncompleteType`/`StructMemberFlexibleArrayInArray`,
  `genTyping.lem:2346-2349` `StructMemberFlexibleArray`: every by-value edge
  INTO a FAM struct is a constraint violation, so that edge cannot close a
  cycle); an `_Alignas(type)` member alignment is completeness-checked by
  `alignof_ty` on the non-agnostic path (`:2851-2871`) — NOT on the
  character-member `Just LT` path (`:2882-2883`, `ailTypesAux.lem:1291-1292`):
  `struct A { _Alignas(struct A) char c; }`, an ISO §6.5.3.4#1 constraint
  violation gcc rejects, is ACCEPTED by the frontend, its table has a by-value
  self-edge, `Acyclic` is FALSE for it, both oracles hang and the Lean wrapper
  fails loudly (`CerbMem.memberAlign: fuel exhausted`) — a frontend GAP
  (C4 pre-merge audit F-A2, upstream-tray candidate), so the guarantee is:
  `Acyclic` holds for every program the frontend ACCEPTS CORRECTLY. Hence at
  the moment a tag's definition is accepted, every tag its members reference
  BY VALUE (through arrays and atomics, never through a pointer or a function
  type) is defined EARLIER: the position in definition order is a rank;
  pointers break the recursion (`struct A { struct B *p; }; struct B { struct
  A a; };` is
  fine). A hand-authored Core file can violate it — which is exactly why the
  hypothesis lives in the obligation, not in the wrapper: on inputs violating
  it the fuel-free wrapper may EXHAUST (the loud sentinel), as the oracle
  itself loops or overflows its stack there.

  Everything here is stated over the LOOKUP the code performs (`lookup`:
  CerbMem's `(fmapElements m).find? (symbolEquality · tag)` — digest+nat,
  description-insensitive; impl_mem.ml's `Pmap.find tag_sym tagDefs`), never
  over the map's internal representation, so no comparator law is needed.
  Ranks are on the looked-up ENTRIES (the stored `Loc × tag_definition`
  values), not on symbols: two symbols that resolve to the same entry share
  its rank by construction.

  MIRROR-OCAML NOTE: a Lean-target reasoning artifact; no OCaml text
  corresponds (fuel is a Lean-target artifact). The predicates are Props
  (they appear only in obligations and in consumers' theorems); the measures
  (`envBound` & co.) are the fuel-free wrappers' arguments and DO execute —
  each is a bound derived in CerbMem_lemMeasureProofs.lean from the code's
  hop structure (the `+ 2`/`+ 3` are hop counts, not budgets).
-/

import Ctype
import CerbTags

set_option autoImplicit false

namespace CerbTagsWf

/-- A stored tag-environment entry: what a lookup returns. -/
abbrev Entry := CerbLocation.Loc × tag_definition

/-- THE lookup of the layout oracle (CerbMem.lean, every tag arm):
    `(fmapElements m).find? (fun (s, _) => symbolEquality s tag)`, the entry
    only. `symbolEquality` is digest+nat, description-INSENSITIVE (OCaml's
    `symbol_compare`/Pmap key order, symbol.lem), NOT the derived BEq. -/
def lookupEntry (m : CerbTags.TagDefsMap) (tag : sym) : Option (sym × Entry) :=
  (fmapElements m).find? (fun (s, _) => symbolEquality s tag)

/-- The entry a tag resolves to (the key dropped). -/
def lookup (m : CerbTags.TagDefsMap) (tag : sym) : Option Entry :=
  (lookupEntry m tag).map Prod.snd

/-- The by-VALUE tag references of a ctype: the tags whose definitions the
    layout recursion ENTERS from a value of this type — through `Array0` and
    `Atomic`; never through `Pointer` (impl_mem.ml:153-158/219-225 return the
    pointer size/alignment without looking at the pointee) or a function
    type (a `panic`/`assert false` arm, no recursion). -/
def refsOf : ctype → List sym
  | Ctype _ (.Struct t) => [t]
  | Ctype _ (.Union0 t) => [t]
  | Ctype _ (.Array0 c _) => refsOf c
  | Ctype _ (.Atomic c) => refsOf c
  | Ctype _ _ => []

/-- A member quadruple as stored in a definition: `(ident, (attrs, alignOpt, quals, ty))`. -/
abbrev Member := identifier × (attributes × Option alignment × qualifiers × ctype)

/-- The type an `_Alignas(type)` override makes the alignment oracle enter
    (`memberAlign`, impl_mem.ml:115-122); `_Alignas(n)` / none enter nothing. -/
def alignTypes : Option alignment → List ctype
  | some (AlignType a) => [a]
  | _ => []

/-- The ctypes a member makes the recursion enter: its own type and its
    `_Alignas(type)` type. -/
def memberTypes1 (m : Member) : List ctype :=
  match m with
  | (_, (_, al, _, ty)) => ty :: alignTypes al

/-- Every ctype a definition makes the layout recursion enter: all members'
    types (with their `_Alignas` types) and, for a struct with a flexible
    array member, that member's element type (offsetsof appends it as an
    ordinary member, impl_mem.ml:104-108; alignof folds
    `Array0 elemTy none` in, :234-239). -/
def memberTypes : tag_definition → List ctype
  | StructDef membrs none => membrs.flatMap memberTypes1
  | StructDef membrs (some (FlexibleArrayMember _ _ _ elemTy)) => membrs.flatMap memberTypes1 ++ [elemTy]
  | UnionDef membrs => membrs.flatMap memberTypes1

/-- The by-value tag references OF a definition (the edges of the graph
    whose acyclicity is the hypothesis). -/
def refsOfDef (d : tag_definition) : List sym := (memberTypes d).flatMap refsOf

/-- `Ranked lookS lookU R`: the entries returned by either lookup descend by
    `R` along every by-value reference that resolves (by either lookup). Two
    lookups because the layout oracle reads struct tags from the THREADED
    map and union tags from the AMBIENT one (impl_mem.ml:173/:255 read the
    global; the CerbMem section header "UPSTREAM ASYMMETRY"); with one map
    for both this is the ordinary one-map rank. -/
def Ranked (lookS lookU : sym → Option Entry) (R : Entry → Nat) : Prop :=
  ∀ (t : sym) (v : Entry), (lookS t = some v ∨ lookU t = some v) →
    ∀ t' ∈ refsOfDef v.2, ∀ (v' : Entry), (lookS t' = some v' ∨ lookU t' = some v') → R v' < R v

/-- ACYCLIC: some rank on entries descends along every by-value reference
    (the "definition order is a rank" invariant of the frontend, stated
    abstractly: any rank will do). THE hypothesis of the one-map layout
    wrappers (`sizeofCtype`, `alignofCtype`, `memberAlign`,
    `offsetsofMembers`, `reconstructValue`). -/
def Acyclic (m : CerbTags.TagDefsMap) : Prop := ∃ R : Entry → Nat, Ranked (lookup m) (lookup m) R

/-- The two-map form for `offsetsof ambient tagDefs`: struct tags resolve in
    `tagDefs`, union tags in `ambient`, ONE rank for both (a cycle crossing
    the two maps — a struct in `tagDefs` containing by value a union of
    `ambient` containing that struct — is excluded; `Acyclic ambient ∧
    Acyclic tagDefs` alone would not exclude it). At elaboration time the
    ambient map is empty (offsetof folds run before the global is populated;
    CerbMem section header) and this is `Acyclic tagDefs`; at run time both
    are the linked program's table and this is `Acyclic` of it (`Acyclic.pair`). -/
def AcyclicPair (ambient tagDefs : CerbTags.TagDefsMap) : Prop :=
  ∃ R : Entry → Nat, Ranked (lookup tagDefs) (lookup ambient) R

theorem Acyclic.pair {m : CerbTags.TagDefsMap} (h : Acyclic m) : AcyclicPair m m := h

/-! ## The measures (execute: the fuel-free wrappers' fuel arguments)

    Every by-value hop of the layout recursion enters an entry of the
    environment at most once along any path (the rank strictly descends), and
    between two hops descends structurally inside one entry's member types.
    So a sufficient fuel is: the structural size of the type asked about, plus
    for every entry of the environment its members' total structural size and
    the constant number of fuel decrements one hop costs. The proof
    (CerbMem_lemMeasureProofs.lean, `pot`/`W`) derives the constants from
    the code: `+ 2` per entry (sizeof → offsetsof → offsetsofMembers →
    sizeof/memberAlign → alignof is the longest hop, whose frames beyond the
    structural ones are two), `+ 1`/`+ 2`/`+ 3` per wrapper for its own
    frames. No budget, no magic value: each term is a derived size or a hop
    count. -/

/-- The structural size a definition contributes: the sum of the sizes of
    every type it makes the recursion enter. -/
def defSize (d : tag_definition) : Nat := ((memberTypes d).map ctype.lemSize).sum

/-- Environments `defsWeight` has been computed for, with their weights, most
    recent first. Each stored map stays alive while it is cached, so its address
    cannot be reused by a different map. -/
private initialize defsWeightCache : IO.Ref (List (CerbTags.TagDefsMap × Nat)) ←
  IO.mkRef []

/-- How many environments `defsWeightImpl` remembers. Execution uses the linked
    table, and offsetsof also passes a second table, so a few entries cover
    every alternation without thrashing. -/
private def defsWeightCacheSize : Nat := 4

/-- Run-time implementation of `defsWeight`: the same sum, computed once per
    environment object. The layout wrappers pass `envBound` (and friends) as
    fuel on every load, store, sizeof and alignof, with the same table each
    time; recomputing the sum walks every member of every tag, so each memory
    operation cost time linear in the whole tag environment.
    Hit: the cached map is the same object as `m` (pointer identity), so its
    stored sum is `defsWeight m`. Miss: the sum is computed exactly as in
    `defsWeight` and remembered. The result is always `defsWeight m`, so fuel,
    verdicts and traces cannot change.
    Trusted assumption (the seam): two `TagDefsMap` values that are the same
    heap object are equal, as for Lean core's `ptrEq`/`withPtrEq`. -/
@[never_extract, noinline]
private unsafe def defsWeightImpl (m : CerbTags.TagDefsMap) : Nat :=
  unsafeBaseIO do
    let cached ← defsWeightCache.get
    match cached.find? (fun (c, _) => ptrAddrUnsafe c == ptrAddrUnsafe m) with
    | some (_, w) => return w
    | none =>
      let w := ((fmapElements m).map (fun p => defSize p.2.2 + 2)).sum
      defsWeightCache.set ((m, w) :: cached.take (defsWeightCacheSize - 1))
      return w

/-- The whole environment's weight: every entry's `defSize` plus the two
    frames a hop into it costs. Executed by `defsWeightImpl`, which caches it
    per environment object; proofs use this definition. -/
@[implemented_by defsWeightImpl]
def defsWeight (m : CerbTags.TagDefsMap) : Nat :=
  ((fmapElements m).map (fun p => defSize p.2.2 + 2)).sum

/-- Measure of `sizeofCtype m ty`, `alignofCtype m ty` and `reconstructValue m … ty …`. -/
def envBound (m : CerbTags.TagDefsMap) (ty : ctype) : Nat := ctype.lemSize ty + defsWeight m + 1

/-- The structural size an `_Alignas` override adds (its type, if a type). -/
def alignSize (al : Option alignment) : Nat := ((alignTypes al).map ctype.lemSize).sum

/-- Measure of `memberAlign m alignOpt ty`. -/
def memberBound (m : CerbTags.TagDefsMap) (al : Option alignment) (ty : ctype) : Nat :=
  ctype.lemSize ty + alignSize al + defsWeight m + 2

/-- The structural size of a member list (types and `_Alignas` types). -/
def membersSize (members : List Member) : Nat :=
  (members.map (fun mb => ctype.lemSize mb.2.2.2.2 + alignSize mb.2.2.1)).sum

/-- Measure of `offsetsofMembers m members`. -/
def membersBound (m : CerbTags.TagDefsMap) (members : List Member) : Nat :=
  membersSize members + defsWeight m + 2

/-- Measure of `offsetsof ambient tagDefs tag _`: the struct's members come
    from `tagDefs` (bounded by its weight once more), the hops below read both. -/
def offsetsofBound (ambient tagDefs : CerbTags.TagDefsMap) : Nat :=
  defsWeight ambient + defsWeight tagDefs + defsWeight tagDefs + 3

end CerbTagsWf
