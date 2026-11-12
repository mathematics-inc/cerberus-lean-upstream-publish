/-
  Concrete memory model for Cerberus.
  Corresponds to: memory/concrete/impl_mem.ml (module Concrete : Memory)

  This matches the OCaml concrete model's types and semantics exactly.
  The concrete model uses simplified types (raw numbers, 2-field pointers)
  compared to the defacto model's symbolic types.
-/

-- pin-bump 2026-09-03 (LemLib 3c88f0d): the MemState maps below are
-- `Std.TreeMap` (arc-6 S3, mirroring impl_mem.ml:93's IntMap = Map.Make(Z));
-- LemLib used to import Std.Data.TreeMap for its own Fmap internals and
-- this file rode on that transitive import. LemLib's Fmap is now the
-- verbatim Pmap port (no Std.TreeMap), so the import is explicit here.
import Std.Data.TreeMap
import Std.Data.TreeSet
import IntegerType
import Ctype
import Symbol
import Mem_common
import Nondeterminism
import CerbFail
import CerbTags
import CerberusImpl
import CerbFloat
import CerbLocation
import Annot
import CerbTagsWf

open CerberusImpl

namespace CerbMem

set_option autoImplicit true

/-! ## Types matching memory/concrete/impl_mem.ml lines 277-525 -/

/-- storage_instance_id = N.num (allocation ID) -/
abbrev StorageInstanceId := Int

/-- symbolic_storage_instance_id (for PNVI-ae-udi) -/
abbrev SymbolicStorageInstanceId := Int

/-- address = N.num (concrete memory address) -/
abbrev Address := Int

/-- Provenance — impl_mem.ml:287-291 -/
inductive Provenance where
  | Prov_none
  | Prov_some (allocId : StorageInstanceId)
  | Prov_symbolic (iota : SymbolicStorageInstanceId) -- only for PNVI-ae-udi
  | Prov_device
  deriving BEq, Inhabited, Repr

/-- pointer_value_base — impl_mem.ml:295-298 -/
inductive PointerValueBase where
  | PVnull (ty : ctype)
  | PVfunction (sym : sym)
  | PVconcrete (unionMember : Option identifier) (addr : Address)
  deriving Inhabited

/-- pointer_value = PV of provenance * pointer_value_base — impl_mem.ml:300-301
    NOTE: 2 fields, NO shift_path (that's the defacto model) -/
inductive PointerValue where
  | PV (prov : Provenance) (base : PointerValueBase)
  deriving Inhabited

/-- integer_value = IV of provenance * Nat_big_num.num — impl_mem.ml:303-304
    The concrete model stores just the raw number, not symbolic integer_value_base -/
inductive IntegerValue where
  | IV (prov : Provenance) (val_ : Int)
  deriving Inhabited

/-- floating_value = float — impl_mem.ml:306-308
    The concrete model uses raw OCaml floats -/
abbrev FloatingValue := Float

/-- mem_value — impl_mem.ml:310-317
    7 constructors (no MVdelayed/MVcomposite — those are defacto model only) -/
inductive MemValue where
  | MVunspecified (ty : ctype)
  | MVinteger (ity : integerType) (iv : IntegerValue)
  | MVfloating (fty : floatingType) (fv : FloatingValue)
  | MVpointer (refTy : ctype) (pv : PointerValue)
  | MVarray (vals : List MemValue)
  | MVstruct (tag : sym) (members : List (identifier × ctype × MemValue))
  | MVunion (tag : sym) (member : identifier) (val_ : MemValue)
  deriving Inhabited

/-! Computable structural size of a `MemValue` (fuel-parameter arc C2,
    2026-09-04): the `fuel_measure` of the generated `loadedValueFromMemValue`
    (core_aux.lem) — a hand-written type has no backend-derived `lemSize`, so
    this is its hand-written twin, in the derived sizes' shape (one per node,
    one per list cons, leaves 0). Kernel-computable; the obligation in
    Core_aux_lemMeasureProofs.lean is proved against it. -/
mutual
def memValueSize : MemValue → Nat
  | .MVunspecified _ => 1
  | .MVinteger _ _ => 1
  | .MVfloating _ _ => 1
  | .MVpointer _ _ => 1
  | .MVarray vals => 1 + memValueListSize vals
  | .MVstruct _ members => 1 + memValueMembersSize members
  | .MVunion _ _ v => 1 + memValueSize v
def memValueListSize : List MemValue → Nat
  | [] => 0
  | v :: vs => 1 + memValueSize v + memValueListSize vs
def memValueMembersSize : List (identifier × ctype × MemValue) → Nat
  | [] => 0
  | (_, _, v) :: vs => 1 + memValueSize v + memValueMembersSize vs
end

/-- footprint = FP of [`W | `R] * address * N.num — impl_mem.ml:523-525 -/
inductive FootprintAccess where | W | R
  deriving BEq, Inhabited, Repr, Ord

inductive Footprint where
  | FP (access : FootprintAccess) (base : Address) (size : Int)
  deriving Inhabited

/-- readonly_status — impl_mem.ml:400-402 -/
inductive ReadonlyStatus where
  | IsWritable
  | IsReadOnly (kind : readonly_kind)
  deriving Inhabited

/-- Abstract byte — impl_mem.ml:415-420 (AbsByte module) -/
structure AbsByte where
  prov : Provenance := .Prov_none
  copyOffset : Option Int := none
  value : Option UInt8 := none
  deriving BEq, Inhabited, Repr

/-- Taint status for PNVI-ae — the allocation's exposure flag,
    impl_mem.ml:409 `taint: [ `Unexposed | `Exposed ]`. -/
inductive Taint where
  | Unexposed
  | Exposed
  deriving BEq, Inhabited

/-- An iota-map entry — impl_mem.ml:490 `iota_map: [ `Single of
    storage_instance_id | `Double of storage_instance_id * storage_instance_id ]
    IntMap.t` (PNVI-ae-udi). `Double` is minted by `addIota` (:903-909), collapsed
    to `Single` by `resolveIota` (:916-942). PNVI arc S2 (2026-10-07). -/
inductive IotaEntry where
  | Single (allocId : StorageInstanceId)
  | Double (allocId1 allocId2 : StorageInstanceId)
  deriving BEq, Inhabited, Repr

/-- The provenance taint a reconstruction returns — the first component of
    `abst`'s result, impl_mem.ml:951 `[`NoTaint | `NewTaint of
    storage_instance_id list]` (produced by `AbsByte.provs_of_bytes`, :462-479;
    consumed by `expose_allocations`, :887-901). NOT the allocation flag
    `Taint` above (OCaml uses the word for both). PNVI arc S2 (2026-10-07). -/
inductive ProvTaint where
  | NoTaint
  | NewTaint (allocIds : List StorageInstanceId)
  deriving BEq, Inhabited, Repr

/-- `find_overlaping`'s result — impl_mem.ml:796-798 `[ `NoAlloc | `SingleAlloc
    of storage_instance_id | `DoubleAlloc of storage_instance_id *
    storage_instance_id ]`. PNVI arc S2 (2026-10-07). -/
inductive OverlapResult where
  | NoAlloc
  | SingleAlloc (allocId : StorageInstanceId)
  | DoubleAlloc (allocId1 allocId2 : StorageInstanceId)
  deriving BEq, Inhabited, Repr

/-- allocation — impl_mem.ml:404-412 -/
structure Allocation where
  base : Address
  size : Int
  ty : Option ctype := none
  isReadonly : ReadonlyStatus := .IsWritable
  taint : Taint := .Unexposed
  prefix_ : prefix0 := PrefOther ""
  deriving Inhabited

/-- A passive concrete load/store receipt; shared shape from mem_common.lem. -/
abbrev AccessReceipt := access_receipt PointerValue MemValue

/-- mem_state — memory/concrete/impl_mem.ml:484–504 (15 fields, including the fork's opt-in, drainable receipt buffer). -/
structure MemState where
  nextAllocId : StorageInstanceId := 0
  nextIota : SymbolicStorageInstanceId := 0
  -- last_address — the allocator's cursor (impl_mem.ml:1252-1263). NO default since the
  -- address-space-bound slice (2026-09-17; [USER 2026-09-16]): the top of the address
  -- space is a PARAMETER of the semantics (`initialMemState addressSpaceTop`, threaded
  -- from the driver's entry), never a literal in a definition; matched mode instantiates
  -- upstream's value from Main.lean `defaultAddressSpaceTop` (`--address-space-top N`).
  lastAddress : Address
  -- arc-6 S3: Std.TreeMap Int (OCaml: IntMap = Map.Make(Z), impl_mem.ml:93);
  -- never enumerated (order-unobserved), keys unique -> results identical to
  -- the previous assoc list at O(log n)
  allocations : Std.TreeMap Int Allocation := Std.TreeMap.empty
  -- iota_map — impl_mem.ml:490 (empty at :513). PNVI arc S2 (2026-10-07): the
  -- OCaml type, `IntMap` of `Single | Double` entries (was `List (Int × Int)`,
  -- "simplified"); a `Std.TreeMap Int`, the same representation as
  -- `allocations`/`bytemap` above (arc-6 S3), keyed by the iota. Written only
  -- by `addIota` (ptrfromint's PNVI arm), `resolveIota` and the collapses of
  -- `diffPtrval`/`effArrayShiftPtrval` (PNVI arc S3); empty at every reachable
  -- default-mode state.
  iotaMap : Std.TreeMap Int IotaEntry := Std.TreeMap.empty
  funptrmap : List (Int × (String × String)) := []
  varargs : List (Int × (Int × List (ctype × PointerValue))) := []
  nextVarargsId : Int := 0
  -- arc-6 S3: same treatment (the S0-profiled secondary hot seam)
  bytemap : Std.TreeMap Int AbsByte := Std.TreeMap.empty
  lastUsedUnionMembers : List (Int × identifier) := []
  -- A set, not a list: every load/store asks `contains`, and every scope
  -- exit adds a killed local, so a list made each access linear in the
  -- number of dead objects so far (quadratic runs). Only
  -- `contains` and `insert` are used, so the order of the OCaml list
  -- (impl_mem.ml dead_allocations) is not observable.
  deadAllocations : Std.TreeSet StorageInstanceId := Std.TreeSet.empty
  dynamicAddrs : List Address := []
  -- last_used — impl_mem.ml:492; written by allocator (:1260), kill
  -- (:1541), load (:1567) and store (:1687), mirrored at each (zero-
  -- discrepancy Z2-M-16 / Z1 audit N2: it was never written here). Its
  -- only READER is the UI state dump `serialise_mem_state` (:2997) —
  -- no batch-path consumer.
  lastUsed : Option StorageInstanceId := none
  requested : List (Address × Int) := []
  observations : Option (List AccessReceipt) := none
  deriving Inhabited

/-- Idempotent enabling preserves any undrained prefix. -/
def beginObserving (st : MemState) : Option MemState :=
  some (match st.observations with
    | none => { st with observations := some [] }
    | some _ => st)

def stopObserving (st : MemState) : MemState := { st with observations := none }

/-- Drain in execution order without disabling capture. No historical states. -/
def takeObservations (st : MemState) : Option (List AccessReceipt × MemState) :=
  st.observations.map fun xs => (xs.reverse, { st with observations := some [] })

/-- Faithful diagnostic view; no scalarization or location equivalence. -/
def viewByte (b : AbsByte) : representation_byte_view :=
  let prov := match b.prov with
    | .Prov_none => .Observed_no_provenance
    | .Prov_some id => .Observed_allocation_provenance id
    | .Prov_symbolic id => .Observed_symbolic_provenance id
    | .Prov_device => .Observed_device_provenance
  .Byte_view prov b.copyOffset (b.value.map fun v => Int.ofNat v.toNat)

/-- Capture work is proportional to the operation's bytes and only occurs when
    enabled. These receipts do not cause suspension or decide success. -/
def recordAccess (loc : CerbLocation.Loc) (kind : access_kind) (ty : ctype)
    (pv : PointerValue) (alloc : Option Int) (addr : Int)
    (bytes : List AbsByte) (value : MemValue) (locking : Option Bool) (st : MemState) : MemState :=
  match st.observations with
  | none => st
  | some xs =>
    { st with observations := some (.Access_receipt loc kind ty pv alloc addr (bytes.map viewByte) value locking :: xs) }

/-! ## Instances

  THE MEMORY-MODEL INSTANCE CAVEAT (arc-14 S1 F4, sem:S1 — relocated here
  from CerbStepInstances.lean:84-94, where it lived scoped to one call
  site and asked future readers to "re-audit").

  The equality instances below are now OCaml-polymorphic-compare PARITY
  (structural, all payloads compared) — the previous coarse forms (PVnull
  compared equal ignoring the ctype; MVstruct compared by tag ignoring
  members; MVinteger/MVfloating/MVpointer/MVunspecified ignored their
  ity/fty/refTy/ctype payloads) diverged silently from OCaml `(=)`.
  Those coarse arms were unreachable from the live core-value equality
  sites (driver.lem:1376,1410 only ever test against the nullary
  Step_blocked2, per CerbStepInstances) — so this enrichment is a no-op
  on today's differential surface (bar-verified zero movement) that
  removes the latent divergence.

  The ORDER instances on the aggregate state types (PointerValue,
  MemValue, MemState) and the equality on Allocation/MemState remain
  DELIBERATELY degenerate, with a REACHABILITY NOTE per the register's
  "OCaml-parity OR loud-failwithI, each with a reachability note" rule:
  none of these types is ever used as a Std.TreeMap/set key or dedup key
  on any path (the concrete model keys its bytemap and allocations by
  `Int`, verified by grep — no ordered/dedup structure is keyed by
  PointerValue/MemValue/MemState/Allocation). A constant `.eq`/`false`
  is therefore never a DECIDING comparison; it exists only to satisfy
  class resolution. Any future code that keys an ordered/dedup structure
  on one of these types MUST replace the corresponding instance with a
  real structural comparator first — that is the standing obligation this
  note records. -/

/-- BEq PointerValueBase — OCaml `(=)` parity: PVnull compares the carried
    ctype; PVconcrete compares the union-member tag AND the address. -/
instance : BEq PointerValueBase where
  beq a b := match a, b with
    | .PVnull t1, .PVnull t2 => t1 == t2
    | .PVfunction s1, .PVfunction s2 => s1 == s2
    | .PVconcrete m1 a1, .PVconcrete m2 a2 => m1 == m2 && a1 == a2
    | _, _ => false

instance : BEq PointerValue where
  beq | .PV p1 b1, .PV p2 b2 => p1 == p2 && b1 == b2

instance : BEq IntegerValue where
  beq | .IV p1 n1, .IV p2 n2 => p1 == p2 && n1 == n2

/-! Structural MemValue equality — OCaml `(=)` parity: every constructor
    compares ALL payloads (ity/fty/refTy/ctype/members); `MVfloating` compares
    its `Float` with `==` (IEEE: NaN ≠ NaN, as OCaml `(=)` on floats). A
    kernel-transparent mutual structural recursion in the `memValueSize` shape
    above (seam-hygiene H3, 2026-09-19): the `unsafe` impl behind an `opaque`
    "sandwich" that stood here for the nested recursion (`beqMemValueSafe`) is
    retired; the two agree on the 23 pinned pairs of
    test/Unit/OpaqueFailureTest.lean (witnessed on the retired impl, record §5).
    A length mismatch is `false` (the pairwise recursion), exactly as the
    retired `length == length && zip.all` was. -/
mutual
def beqMemValue : MemValue → MemValue → Bool
  | .MVunspecified t1, .MVunspecified t2 => t1 == t2
  | .MVinteger ity1 v1, .MVinteger ity2 v2 => ity1 == ity2 && v1 == v2
  | .MVfloating fty1 v1, .MVfloating fty2 v2 => fty1 == fty2 && v1 == v2
  | .MVpointer t1 v1, .MVpointer t2 v2 => t1 == t2 && v1 == v2
  | .MVarray e1, .MVarray e2 => beqMemValueList e1 e2
  | .MVstruct t1 ms1, .MVstruct t2 ms2 => t1 == t2 && beqMemValueMembers ms1 ms2
  | .MVunion t1 m1 v1, .MVunion t2 m2 v2 => t1 == t2 && m1 == m2 && beqMemValue v1 v2
  | _, _ => false
def beqMemValueList : List MemValue → List MemValue → Bool
  | [], [] => true
  | a :: as, b :: bs => beqMemValue a b && beqMemValueList as bs
  | _, _ => false
def beqMemValueMembers : List (identifier × ctype × MemValue) → List (identifier × ctype × MemValue) → Bool
  | [], [] => true
  | (i1, c1, v1) :: r1, (i2, c2, v2) :: r2 => i1 == i2 && c1 == c2 && beqMemValue v1 v2 && beqMemValueMembers r1 r2
  | _, _ => false
end

instance : BEq MemValue where beq := beqMemValue
instance : BEq Footprint where
  beq | .FP a1 b1 s1, .FP a2 b2 s2 => a1 == a2 && b1 == b2 && s1 == s2
instance : Ord Footprint where
  compare | .FP _ b1 _, .FP _ b2 _ => compare b1 b2
instance : Ord IntegerValue where compare | .IV _ n1, .IV _ n2 => compare n1 n2
-- Degenerate-by-design (see the reachability note above): never a set/map
-- key on any path.
instance : Ord PointerValue where compare _ _ := .eq
instance : Ord MemValue where compare _ _ := .eq
instance : BEq Allocation where beq _ _ := false
instance : BEq MemState where beq _ _ := false
instance : Ord MemState where compare _ _ := .eq

/-! ## Helper: construct ctype with empty annotations -/

def mkCtype (ty_ : ctype_) : ctype := Ctype ([] : List annot) ty_

/-- The one PNVI refusal message (PNVI arc; design record
    docs/2026-10-04_pnvi-ae-udi-design.md §D.5, §G.1; the shape ruled in §H
    for §F.16: "(a) is fine" — the `CerbFS` `failwithI`-with-a-fixed-prefix
    shape, `CerbFS.lean` `fsRefusal`). `detail` names the `R-PNVI-nn` row,
    the site, the impl_mem.ml line and upstream's text. [USER 2026-10-05]:
    "Re PNVI - agree on your recs except for mirroring crashes / obviously wrong
    behavior. These should be refusals surely?" — an upstream crash or
    self-declared-wrong arm on the PNVI path is refused here, never
    mirrored. Every site is unreachable at the default switch set. -/
def pnviRefusal (detail : String) : String :=
  s!"PNVI_ae_udi refusal (unsupported upstream arm): {detail} — refused, not mirrored (upstream crashes, debug-print arms and self-declared-wrong arms on the PNVI path are loud refusals: design record docs/2026-10-04_pnvi-ae-udi-design.md §G/§H)"

/-! ## combine_prov — impl_mem.ml:366-394 -/

def combineProv : Provenance → Provenance → Provenance
  | .Prov_none, .Prov_none => .Prov_none
  | .Prov_none, .Prov_some id => .Prov_some id
  | .Prov_none, .Prov_device => .Prov_device
  | .Prov_some id, .Prov_none => .Prov_some id
  | .Prov_some id1, .Prov_some id2 =>
    if id1 == id2 then .Prov_some id1 else .Prov_none
  | .Prov_some _, .Prov_device => .Prov_device
  | .Prov_device, .Prov_none => .Prov_device
  | .Prov_device, .Prov_some _ => .Prov_device
  | .Prov_device, .Prov_device => .Prov_device
  -- impl_mem.ml:390-394 `(* PNVI-ae-udi *) (* TODO: this is improvised, need to
  -- check with P *) | (Prov_symbolic _, _) | (_, Prov_symbolic _) -> failwith
  -- "Concrete.combine_prov: found a Prov_symbolic"` — an upstream crash on the PNVI
  -- path (the oracle hits it on 4 of its own 44 PNVI litmus files, design §C.2),
  -- REFUSED (design §G.1 row R1, class (A), `R-PNVI-01`; PNVI arc S3). Unreachable
  -- at the default switch set (nothing mints `Prov_symbolic` there)
  | .Prov_symbolic _, _ => failwithI (pnviRefusal "R-PNVI-01: combine_prov, a Prov_symbolic provenance (first argument) — impl_mem.ml:390-394 `(* TODO: this is improvised, need to check with P *)` … `failwith \"Concrete.combine_prov: found a Prov_symbolic\"`")
  | _, .Prov_symbolic _ => failwithI (pnviRefusal "R-PNVI-01: combine_prov, a Prov_symbolic provenance (second argument) — impl_mem.ml:390-394 `(* TODO: this is improvised, need to check with P *)` … `failwith \"Concrete.combine_prov: found a Prov_symbolic\"`")

/-! ## Layout computation — impl_mem.ml:98-273 (offsetsof / sizeof / alignof)

    OCaml's sizeof/alignof take `?(tagDefs= Tags.tagDefs ())` (optional,
    defaulting to the global) and offsetsof takes tagDefs explicitly;
    the family THREADS `~tagDefs` through every recursive call
    (impl_mem.ml:111-119 `sizeof ~tagDefs`/`alignof ~tagDefs`, :150
    :160 :168-169 :214 :226 etc.). The Lean workers mirror that: an
    explicit `tagDefs` parameter threaded through the mutual block; the
    default-budget wrappers supply `CerbTags.tagDefs ()`, mirroring the
    OCaml optional-arg default (every impl_mem-internal NON-layout call
    site uses the default).
    The threading is semantically LIVE at elaboration time: the
    AilEoffsetof fold (translation.lem:2730 → offsetof_ival,
    impl_mem.ml:2193) runs BEFORE the Tags global is populated
    (main.ml:304-305 sets it post-elaboration), so nested-struct
    offsetof resolves ONLY through the threaded map. The pre-fix Lean
    ambient-read shortcut panicked exactly there (pr44468, the CI
    sweep's finding; 2026-09-01 S-basket item 1).
    UPSTREAM ASYMMETRY, MIRRORED DELIBERATELY: the Union arms of both
    sizeof and alignof look the tag up in the GLOBAL
    (`Pmap.find tag_sym (Tags.tagDefs ())`, impl_mem.ml:173, :255)
    even though their member folds thread ~tagDefs — so
    elaboration-time offsetof over a union-containing struct CRASHES
    upstream (probed 2026-09-01: oracle exit 125, "Tags definitions
    must be set"; Lean mirrors with the unknown-tag panic — immaculate
    row offsetof-union-member pins the pair). Upstream-tray candidate.

    Integer/float leaf sizes come from CerberusImpl (the DefaultImpl port),
    exactly like OCaml routes them through `(Ocaml_implementation.get ())`
    — no local size constants are kept here.

    DECLARED (zero-discrepancy Z2-M-11): the layout family computes on
    Nat where the OCaml computes on Z — `al_n.toNat` (memberAlign's
    _Alignas arm, impl_mem.ml:118 `al_n`; alignof's folds read it through
    `Z.to_int al_n`, :248/:267, which raises Overflow on a huge _Alignas —
    REACHABLE (a front-end-accepted `_Alignas(2^62)`) and registered as
    ISO-fix register R7, the R3 class: Lean computes the unbounded answer,
    see `alignofCtype_lemFuel`), `lastOffset % align` /
    `maxOffset % align` / `maxSize % maxAlign` (:123/:169-171/:189-191
    `Z.modulus … 0` raises Division_by_zero where Lean's `% 0` is the
    identity), `n.toNat * sizeof` (:151 `Z.mul n`). Reachability of any
    difference: an alignment of 0 or a negative array size. Alignments
    come from alignof (≥ 1 for every complete type) or from a front-end-
    validated `_Alignas` (≥ 1 or a type); array sizes are front-end
    non-negative; the member-less struct that would make an alignment 0
    is UB061 on the shared front end (tests/z2-probes/mem/empty_struct.c:
    UB061 on fork, upstream and Lean). Unreachable by construction. -/

/-- `(Ocaml_implementation.get ()).sizeof_pointer` — impl_mem.ml:153-158 (and
    :219-225 alignof_pointer, :1160-1164, :2134): `None -> failwith "the
    concrete memory model requires a complete implementation"`. Read from the
    CerberusImpl record mirror (zero-discrepancy literal census #2: was the
    literal 8). alignof_pointer = sizeof_pointer = 8 in DefaultImpl. -/
def targetPtrSize : Nat :=
  match CerberusImpl.sizeof_pointer with
  | some n => n
  | none => failwithI "CerbMem.targetPtrSize: the concrete memory model requires a complete implementation"

/- The threaded tag environment is the Fmap itself (the same value the
   ambient global holds); enumeration-spine conversion happens only at
   the tag-LOOKUP arms (`CerbTagsWf.lookupEntry` = `fmapElements … |>.find?
   symbolEquality`, the exact pre-threading per-arm lookup named ONCE so
   the C4 sufficiency proofs can speak about it; leaf-type sizeof/alignof
   pay no conversion). -/
private abbrev TagDefs := CerbTags.TagDefsMap

/- The enum map (program-data parameters E-A, 2026-09-20): the value of the
   lem reader `Implementation.enum_definitions`, received by every
   reader_consumer stub below as its FIRST leading parameter (sorted reader
   order: enum_definitions, then tagDefs) and threaded to every leaf that
   resolves an `Enum` — exactly where impl_mem.ml resolves one through the
   DefaultImpl registry (`CerberusImpl.resolveEnum`; the type-only layout reps
   `CerberusImpl.sizeof_ity`/`is_signed_ity`/`alignof_ity` then see a
   resolved type). -/
private abbrev EnumDefs := CerberusImpl.EnumDefs

/-! ARC-7 S4 TOTALIZATION (fuel; arc-3 pattern): the layout oracles and
    the (de)serializers below were `partial def`s — kernel-opaque, no
    equations: nothing could compute through a memory operation by
    unfolding, and the exec-totality gate requires equations. Each is now a fuel'd
    worker `*_lemFuel` (fuel decremented once per recursion layer;
    exhaustion = the OPAQUE `fuelExhaustedWith` sentinel, LemLib —
    a fake value provable equal to something would be a lie, D4
    transparency doctrine) + the original name as the wrapper started at
    the AMBIENT fuel (`[LemFuel]`, `LemFuel.fuel` — the fuel-parameter arc
    2026-09-04: the caller's parameter, never a constant; the former
    `lemDefaultFuel` is deleted), rfl-defeq to the worker at every
    instance, so every call site and every runtime behavior at a
    sufficient fuel is unchanged. `stringFromMemValue` (pp-only, never
    on a computed path) is total since arc-10 S3 (structural mutual
    recursion — no fuel needed). C4 (2026-09-05): the five layout
    wrappers below the block are MEASURED (fuel-free) under the
    acyclicity hypothesis — see their header. -/

mutual

/-- Member alignment with the `align_opt` (_Alignas) override —
    impl_mem.ml:115-122 (the align_opt match inside offsetsof; the same
    three-way match is repeated verbatim at impl_mem.ml:179-186 for union
    sizeof and inside the struct/union alignof folds). -/
def memberAlign_lemFuel (lemFuel : Nat) (enumDefs : EnumDefs) (ambient : TagDefs) (tagDefs : TagDefs)
    (alignOpt : Option alignment) (ty : ctype) : Nat :=
  match lemFuel with
  | 0 => fuelExhaustedWith "CerbMem.memberAlign: fuel exhausted" 1
  | lemFuel + 1 =>
    match alignOpt with
    | none => alignofCtype_lemFuel lemFuel enumDefs ambient tagDefs ty
    | some (AlignInteger al_n) => al_n.toNat
    | some (AlignType al_ty) => alignofCtype_lemFuel lemFuel enumDefs ambient tagDefs al_ty

/-- THE struct-layout oracle: fold over the raw member quadruples,
    padding each member up to its (possibly _Alignas-overridden)
    alignment. Mirrors the fold at impl_mem.ml:112-127. Returns
    ([(ident, ty, offset)], last_offset) where last_offset is the end of
    the last member BEFORE trailing padding — exactly OCaml's `maxoffset`.
    (Alignment 0 is impossible for valid C members; Lean's `% 0 = id` +
    truncated subtraction make it degrade to pad = 0 instead of OCaml's
    Division_by_zero.) -/
def offsetsofMembers_lemFuel (lemFuel : Nat) (enumDefs : EnumDefs) (ambient : TagDefs) (tagDefs : TagDefs)
    (members : List (identifier × (attributes × Option alignment × qualifiers × ctype)))
    : List (identifier × ctype × Nat) × Nat :=
  match lemFuel with
  | 0 => fuelExhaustedWith "CerbMem.offsetsofMembers: fuel exhausted" ([], 0)
  | lemFuel + 1 =>
    let (xs, maxoffset) := members.foldl (init := (([] : List (identifier × ctype × Nat)), 0))
      fun (acc : List (identifier × ctype × Nat) × Nat) memb =>
        let (xs, lastOffset) := acc
        let (ident, (_, alignOpt, _, ty)) := memb
        let size := sizeofCtype_lemFuel lemFuel enumDefs ambient tagDefs ty          -- impl_mem.ml:112 (sizeof ~tagDefs)
        let align := memberAlign_lemFuel lemFuel enumDefs ambient tagDefs alignOpt ty -- impl_mem.ml:113-119 (alignof ~tagDefs)
        let x := lastOffset % align                   -- impl_mem.ml:123
        let pad := if x == 0 then 0 else align - x    -- impl_mem.ml:124
        ((ident, ty, lastOffset + pad) :: xs, lastOffset + pad + size)  -- impl_mem.ml:125
    (xs.reverse, maxoffset)

/-- offsetsof — impl_mem.ml:98-129. Struct: offsetsofMembers over the
    member list, with the flexible array member appended as an ordinary
    member (its stored element ctype, verbatim per impl_mem.ml:104-108)
    unless `ignoreFlexible`. Union: every member at offset 0, last_offset
    0 (impl_mem.ml:128-129). Missing tag: OCaml's Pmap.find raises
    Not_found — panic here.
    Tag lookup uses symbolEquality (digest+nat, description-INSENSITIVE
    — OCaml's symbol_compare/Pmap key order, symbol.lem), NOT the derived
    BEq which also compares the description. Same for every tag lookup in
    this file. -/
def offsetsof_lemFuel (lemFuel : Nat) (enumDefs : EnumDefs) (ambient : TagDefs) (tagDefs : TagDefs) (tagSym : sym)
    (ignoreFlexible : Bool := false) : List (identifier × ctype × Nat) × Nat :=
  match lemFuel with
  | 0 => fuelExhaustedWith "CerbMem.offsetsof: fuel exhausted" ([], 0)
  | lemFuel + 1 =>
    match CerbTagsWf.lookupEntry tagDefs tagSym with
    | none => failwithI "CerbMem.offsetsof: unknown tag (OCaml: Pmap.find Not_found)"
    | some (_, (_, StructDef membrs_ flexibleOpt)) =>
      let membrs := match flexibleOpt with
        | none => membrs_
        | some (FlexibleArrayMember attrs ident qs ty) =>
          if ignoreFlexible then membrs_
          else membrs_ ++ [(ident, (attrs, none, qs, ty))]  -- impl_mem.ml:107-108 (raw stored ctype)
      offsetsofMembers_lemFuel lemFuel enumDefs ambient tagDefs membrs
    | some (_, (_, UnionDef membrs)) =>
      (membrs.map (fun (ident, (_, _, _, ty)) => (ident, ty, 0)), 0)

/-- sizeof — impl_mem.ml:131-194.
    Struct (impl_mem.ml:162-171): offsetsof last_offset (ignore_flexible —
    the flexible member is uncounted except through alignof's trailing
    padding), padded up to alignof(struct).
    Union (impl_mem.ml:172-192): max member size padded up to max member
    alignment (align_opt honored).
    Void/incomplete-Array/Function PANIC, mirroring OCaml `assert false`
    (impl_mem.ml:134-135) — a 0-sized value flowing onward is the
    panic-optimized-into-value hazard (arc-14 S1 F1, sem:S7; the previous
    "return 0" divergence carried provenance, not a rationale). -/
def sizeofCtype_lemFuel (lemFuel : Nat) (enumDefs : EnumDefs) (ambient : TagDefs) (tagDefs : TagDefs) (cty : ctype) : Nat :=
  match lemFuel with
  | 0 => fuelExhaustedWith "CerbMem.sizeofCtype: fuel exhausted" 0
  | lemFuel + 1 =>
    match cty with
    | Ctype _ ty_ =>
      match ty_ with
      | .Void0 => failwithI "CerbMem.sizeofCtype: Void (impl_mem.ml:134-135 assert false)"
      | .Array0 _ none => failwithI "CerbMem.sizeofCtype: incomplete array (impl_mem.ml:134-135 assert false)"
      | .Function _ _ _ | .FunctionNoParams _ =>
        failwithI "CerbMem.sizeofCtype: function type (impl_mem.ml:134-135 assert false)"
      | .Basic (.Integer ity) =>
        match CerberusImpl.sizeof_ity (CerberusImpl.resolveEnum enumDefs ity) with      -- impl_mem.ml:136-141
        | some n => n
        | none => failwithI "CerbMem.sizeofCtype: the concrete memory model requires a complete implementation sizeof INTEGER"
      | .Basic (.Floating fty) =>
        match CerberusImpl.sizeof_fty fty with      -- impl_mem.ml:143-148
        | some n => n
        | none => failwithI "CerbMem.sizeofCtype: the concrete memory model requires a complete implementation sizeof FLOAT"
      | .Array0 elemCty (some n) => n.toNat * sizeofCtype_lemFuel lemFuel enumDefs ambient tagDefs elemCty  -- impl_mem.ml:150-151 (sizeof ~tagDefs)
      | .Pointer _ _ => targetPtrSize               -- impl_mem.ml:153-158
      | .Atomic innerCty => sizeofCtype_lemFuel lemFuel enumDefs ambient tagDefs innerCty    -- impl_mem.ml:160-161 (sizeof ~tagDefs)
      | .Struct tagSym =>                           -- impl_mem.ml:162-171
        let (_, maxOffset) := offsetsof_lemFuel lemFuel enumDefs ambient tagDefs tagSym (ignoreFlexible := true)  -- impl_mem.ml:168 (threaded)
        let align := alignofCtype_lemFuel lemFuel enumDefs ambient tagDefs cty  -- impl_mem.ml:169 (alignof ~tagDefs)
        let x := maxOffset % align
        if x == 0 then maxOffset else maxOffset + (align - x)
      | .Union0 tagSym =>                           -- impl_mem.ml:172-192
        -- GLOBAL read, deliberately: impl_mem.ml:173 is
        -- `Pmap.find tag_sym (Tags.tagDefs ())` — NOT ~tagDefs (the
        -- upstream asymmetry; see the section header note).
        match CerbTagsWf.lookupEntry ambient tagSym with
        | some (_, (_, UnionDef membrs)) =>
          let (maxSize, maxAlign) := membrs.foldl (init := ((0 : Nat), (0 : Nat)))
            fun (acc : Nat × Nat) memb =>
              let (accSize, accAlign) := acc
              let (_, (_, alignOpt, _, ty)) := memb
              (max accSize (sizeofCtype_lemFuel lemFuel enumDefs ambient tagDefs ty),
               max accAlign (memberAlign_lemFuel lemFuel enumDefs ambient tagDefs alignOpt ty))
          -- trailing padding up to the max alignment — impl_mem.ml:189-191
          let x := maxSize % maxAlign
          if x == 0 then maxSize else maxSize + (maxAlign - x)
        | _ => failwithI "CerbMem.sizeofCtype: Union tag not a UnionDef (OCaml: assert false / Not_found)"
      | .Byte => 1                                  -- impl_mem.ml:193-194

/-- alignof — impl_mem.ml:196-273.
    Struct (impl_mem.ml:228-252): max member alignment (align_opt
    honored), the fold seeded with the flexible array member's
    array-of-element alignment when present (else 0).
    Union (impl_mem.ml:253-271): max member alignment, seed 0.
    Void/Function PANIC, mirroring OCaml `assert false` (impl_mem.ml:
    198-199, 216-218) — arc-14 S1 F1, sem:S7 (was: silent 1,
    provenance-only). -/
def alignofCtype_lemFuel (lemFuel : Nat) (enumDefs : EnumDefs) (ambient : TagDefs) (tagDefs : TagDefs) (cty : ctype) : Nat :=
  match lemFuel with
  | 0 => fuelExhaustedWith "CerbMem.alignofCtype: fuel exhausted" 1
  | lemFuel + 1 =>
    match cty with
    | Ctype _ ty_ =>
      match ty_ with
      | .Void0 => failwithI "CerbMem.alignofCtype: Void (impl_mem.ml:198-199 assert false)"
      | .Function _ _ _ | .FunctionNoParams _ =>
        failwithI "CerbMem.alignofCtype: function type (impl_mem.ml:216-218 assert false)"
      | .Basic (.Integer ity) =>
        match CerberusImpl.alignof_ity (CerberusImpl.resolveEnum enumDefs ity) with     -- impl_mem.ml:200-206
        | some n => n
        | none => failwithI "CerbMem.alignofCtype: the concrete memory model requires a complete implementation alignof INTEGER"
      | .Basic (.Floating fty) =>
        match CerberusImpl.alignof_fty fty with     -- impl_mem.ml:207-213
        | some n => n
        | none => failwithI "CerbMem.alignofCtype: the concrete memory model requires a complete implementation alignof FLOATING"
      | .Array0 elemCty _ => alignofCtype_lemFuel lemFuel enumDefs ambient tagDefs elemCty   -- impl_mem.ml:214-215 (alignof ~tagDefs)
      | .Pointer _ _ => targetPtrSize               -- impl_mem.ml:219-225
      | .Atomic innerCty => alignofCtype_lemFuel lemFuel enumDefs ambient tagDefs innerCty   -- impl_mem.ml:226-227 (alignof ~tagDefs)
      | .Struct tagSym =>                           -- impl_mem.ml:228-252
        -- threaded lookup: impl_mem.ml:229 is `Pmap.find tag_sym tagDefs`
        match CerbTagsWf.lookupEntry tagDefs tagSym with
        | some (_, (_, StructDef membrs flexibleOpt)) =>
          let init := match flexibleOpt with        -- impl_mem.ml:234-239
            | none => 0
            | some (FlexibleArrayMember _ _ _ elemTy) =>
              alignofCtype_lemFuel lemFuel enumDefs ambient tagDefs (mkCtype (.Array0 elemTy none))
          membrs.foldl (init := init) fun acc memb =>
            let (_, (_, alignOpt, _, ty)) := memb
            -- ISO-fix register R7 (VALIDATION.md §2; the R3 class, [USER 2026-10-03]
            -- rulings): impl_mem.ml:248 reads an `AlignInteger al_n` through
            -- `Z.to_int al_n`, which raises Z.Overflow outside OCaml's native int
            -- range; upstream's own Lem interface is unbounded (implementation.lem:27
            -- `alignof_ty … -> maybe nat`, mem.lem:191 `alignof_ival`), so the
            -- unbounded maximum is computed here (pins zd-ta-alignas-huge-*).
            max (memberAlign_lemFuel lemFuel enumDefs ambient tagDefs alignOpt ty) acc  -- impl_mem.ml:242-251
        | _ => failwithI "CerbMem.alignofCtype: Struct tag not a StructDef (OCaml: assert false / Not_found)"
      | .Union0 tagSym =>                           -- impl_mem.ml:253-271
        -- GLOBAL read, deliberately: impl_mem.ml:255 is
        -- `Pmap.find tag_sym (Tags.tagDefs ())` — NOT ~tagDefs (the
        -- upstream asymmetry; see the section header note).
        match CerbTagsWf.lookupEntry ambient tagSym with
        | some (_, (_, UnionDef membrs)) =>
          membrs.foldl (init := (0 : Nat)) fun acc memb =>
            let (_, (_, alignOpt, _, ty)) := memb
            -- ISO-fix register R7: as the struct fold (impl_mem.ml:267 `Z.to_int al_n`)
            max (memberAlign_lemFuel lemFuel enumDefs ambient tagDefs alignOpt ty) acc
        | _ => failwithI "CerbMem.alignofCtype: Union tag not a UnionDef (OCaml: assert false / Not_found)"
      | .Byte => 1                                  -- impl_mem.ml:272-273

end

/-! FUEL-PARAMETER ARC C4 (2026-09-05): the five layout wrappers are
    MEASURED, fuel-FREE, under the hypothesis `CerbTagsWf.Acyclic ambient`
    (`AcyclicPair ambient tagDefs` for `offsetsof`, whose struct tags resolve
    in the threaded map and union tags in the ambient one). The measure is
    `CerbTagsWf.envBound`/`memberBound`/`membersBound`/`offsetsofBound`: the
    structural size of what is asked about plus the environment's weight
    (every entry's member-type sizes + 2 frames per hop) — derived from the
    hop structure in CerbMem_lemMeasureProofs.lean, where the obligations
    `<f>_measure_sufficient (…) (lemHyp : Acyclic …) (lemFuel) (lemMeasureLe :
    μ ≤ lemFuel) : f_lemFuel lemFuel … = f …` are proved in the generated
    `assuming` shape. On an environment violating the hypothesis (a by-value
    cycle a hand-authored Core file can state; the C frontend never emits one —
    CerbTagsWf's header cites the invariant) the wrapper may exhaust: the loud
    `fuelExhaustedWith` sentinel, where the oracle loops. tagDefs: the ambient
    global, mirroring OCaml's `?(tagDefs= Tags.tagDefs ())` optional-arg
    default (unchanged). -/
def memberAlign (enumDefs : EnumDefs) (ambient : TagDefs) (alignOpt : Option alignment) (ty : ctype) : Nat :=
  memberAlign_lemFuel (CerbTagsWf.memberBound ambient alignOpt ty) enumDefs ambient ambient alignOpt ty

/-- Measured + default-tagDefs wrapper (see memberAlign). -/
def offsetsofMembers (enumDefs : EnumDefs) (ambient : TagDefs)
    (members : List (identifier × (attributes × Option alignment × qualifiers × ctype)))
    : List (identifier × ctype × Nat) × Nat :=
  offsetsofMembers_lemFuel (CerbTagsWf.membersBound ambient members) enumDefs ambient ambient members

/-- Measured wrapper (tagDefs explicit, like OCaml offsetsof; hypothesis
    `AcyclicPair ambient tagDefs`). -/
def offsetsof (enumDefs : EnumDefs) (ambient : TagDefs) (tagDefs : TagDefs) (tagSym : sym)
    (ignoreFlexible : Bool := false) : List (identifier × ctype × Nat) × Nat :=
  offsetsof_lemFuel (CerbTagsWf.offsetsofBound ambient tagDefs) enumDefs ambient tagDefs tagSym ignoreFlexible

/-- Measured + default-tagDefs wrapper (see memberAlign). -/
def sizeofCtype (enumDefs : EnumDefs) (ambient : TagDefs) (cty : ctype) : Nat :=
  sizeofCtype_lemFuel (CerbTagsWf.envBound ambient cty) enumDefs ambient ambient cty

/-- Measured + default-tagDefs wrapper (see memberAlign). -/
def alignofCtype (enumDefs : EnumDefs) (ambient : TagDefs) (cty : ctype) : Nat :=
  alignofCtype_lemFuel (CerbTagsWf.envBound ambient cty) enumDefs ambient ambient cty

/-! ## Byte-level serialization

    Integer signedness comes from CerberusImpl.is_signed_ity (the
    DefaultImpl port) — the local isSignedIty duplicate that disagreed on
    Wchar_t/Enum is deleted (survey finding 17). -/

/-- bytes_of_int — impl_mem.ml:1096-1113: `size` little-endian bytes of
    `val_`'s two's complement (`Z.extract i (8*n) 8`, :1110-1112), AFTER
    the range assert (:1105-1109): `assert false` — preceded by a
    diagnostic `Printf.printf "failed: bytes_of_int…"` on the TOOL's
    stdout, not mirrored — unless `min ≤ i ≤ max` for the signedness
    (`[-2^(nbits-1), 2^(nbits-1)-1]` signed, `[0, 2^nbits-1]` unsigned)
    and `nbits ≤ 128`. Zero-discrepancy Z-16: the assert is mirrored as a
    fail-stop (Q4); this used to wrap silently. Unreachable from C
    (`conv_int` precedes every store; every repr call site passes the
    OCaml's own signedness, :1147/:1153/:1183/:1189). -/
def intToBytes (signed : Bool) (val_ : Int) (size : Nat) : List (Option UInt8) :=
  let totalBits := size * 8
  let modulusVal : Int := 1 <<< totalBits
  let half : Int := (1 : Int) <<< (totalBits - 1)
  let lo : Int := if signed then -half else 0
  let hi : Int := (if signed then half else modulusVal) - 1
  if !(lo ≤ val_ && val_ ≤ hi) || totalBits > 128 then
    failwithI s!"CerbMem.intToBytes: failed: bytes_of_int({if signed then "signed" else "unsigned"}), i= {val_}, nbits= {totalBits}, [{lo} ... {hi}] (impl_mem.ml:1105-1109 assert false)"
  else
  let unsigned : Int := if val_ < 0 then modulusVal + val_ else val_
  List.range size |>.map fun i =>
    let shifted := unsigned >>> (i * 8)
    some (shifted.toNat % 256).toUInt8

/-- int_of_bytes — impl_mem.ml:739-760 (called only on fully specified
    byte lists: abst's `extract_unspec` returns `None` first, :951-958,
    which is the `none` arm here). OCaml `assert false` on `[]` (:742-743)
    and on more than 16 bytes (:744-745) — mirrored as fail-stops
    (zero-discrepancy Z-16, Q4); unreachable by construction (every
    integer type has 1 ≤ sizeof ≤ 8, and loads are sizeof-sliced). -/
def bytesToInt (bytes : List AbsByte) (signed : Bool) : Option Int :=
  if bytes.any (·.value.isNone) then none
  else if bytes.isEmpty then failwithI "Concrete.int_of_bytes: [] (impl_mem.ml:742-743 assert false)"
  else if bytes.length > 16 then failwithI "Concrete.int_of_bytes: more than 16 bytes (impl_mem.ml:744-745 assert false)"
  else
    let rec go (bs : List AbsByte) (i : Nat) (acc : Int) : Int :=
      match bs with
      | [] => acc
      | b :: rest =>
        let contribution : Int := match b.value with
          | some v => (v.toNat : Int) <<< (i * 8)
          | none => 0
        go rest (i + 1) (acc + contribution)
    let val_ := go bytes 0 0
    if signed && bytes.length > 0 then
      let bits := bytes.length * 8
      let signBit : Int := 1 <<< (bits - 1)
      if val_ >= signBit then some (val_ - (1 <<< bits)) else some val_
    else some val_

/-- INTEGER-load provenance policy — AbsByte.pvi_split_bytes,
    impl_mem.ml:455-460: fold combine_prov over the bytes' provenances
    starting from Prov_none, in OCaml's exact argument order
    (`combine_prov b.prov prov_acc`) — the order matters: e.g.
    [some 1, some 2, some 2] folds to Prov_some 2, not Prov_none.
    Used by the Basic-Integer (impl_mem.ml:949-960) and Byte
    (impl_mem.ml:961-973) arms of abst. -/
def provFromIntegerBytes (bytes : List AbsByte) : Provenance :=
  bytes.foldl (fun acc b => combineProv b.prov acc) .Prov_none

/-- POINTER-load provenance policy — AbsByte.split_bytes,
    impl_mem.ml:432-453: the provenance is the bytes' SHARED provenance
    (`VALID p1, p2 when p1 = p2` fold) — any two differing provenances
    (including Prov_none vs Prov_some) collapse to Prov_none. Returns the
    ValidPtrProv status too: `ValidPtrProv` iff the provenances are all
    equal (`VALID`) AND the copy_offsets are consecutive from 0 (`PtrBytes`)
    — impl_mem.ml:443-453 (`VALID z, PtrBytes _ -> ValidPtrProv`; `VALID z, _`
    and `INVALID, _` -> `NotValidPtrProv`). OCaml consults it ONLY under
    is_PNVI () (the pointer arm of abst, impl_mem.ml:1057-1088), i.e. in
    `reconstructValueAbst_lemFuel`'s `is_PNVI` branch; the default branch
    uses .1 alone (impl_mem.ml:1087-1088 `else prov`).
    PNVI arc S2 (2026-10-07): the status used to ignore the `INVALID` case
    (consecutive offsets over differing provenances gave `true`); it had no
    consumer then, so the fix moves nothing (`.1` and its text are unchanged).
    Empty byte list: OCaml failwith (impl_mem.ml:433-434) — mirrored. -/
def splitBytesProv (bytes : List AbsByte) : Provenance × Bool :=
  match bytes with
  | [] => failwithI "Concrete.AbsByte.split_bytes: called on an empty list"
  | b :: _ =>
    let prov := if bytes.all (fun b' => b'.prov == b.prov) then b.prov else .Prov_none
    let validPtr := bytes.all (fun b' => b'.prov == b.prov) && (bytes.zipIdx.all fun (b', i) =>
      match b'.copyOffset with
      | some off => off == (i : Int)
      | none => false)
    (prov, validPtr)

/-- AbsByte.provs_of_bytes — impl_mem.ml:462-479 (PNVI-ae-udi): the
    allocation ids of the bytes' `Prov_some` provenances, in OCaml's order
    (a `fold_left` that conses, so the LAST byte's id comes first);
    `NoTaint` when there are none. Consumed only by `expose_allocations`
    (impl_mem.ml:1602-1606, load, under `PNVI AE ∨ AE_UDI`).
    The `Prov_symbolic iota -> acc (* TODO(iota) *)` arm (:470-471) is
    REFUSED (design §G.1 row R2, `R-PNVI-01b`): it is shadowed — abst's
    integer and byte arms run `pvi_split_bytes` (:986/:999) on the same bytes
    first, whose `combine_prov` raises on a `Prov_symbolic` (:390-394, row
    R1) — so the arm is reached only past an upstream crash. Unreachable at
    the default switch set (no `Prov_symbolic` is ever minted there). -/
def provsOfBytes (bytes : List AbsByte) : ProvTaint :=
  let xs := bytes.foldl (fun (acc : List StorageInstanceId) b =>
    match b.prov with
    | .Prov_none => acc
    | .Prov_some allocId => allocId :: acc
    | .Prov_symbolic _ =>
      failwithI (pnviRefusal "R-PNVI-01b: AbsByte.provs_of_bytes, Prov_symbolic byte — impl_mem.ml:470-471 `Prov_symbolic iota -> acc (* TODO(iota) *)`, reached only after combine_prov's `failwith \"Concrete.combine_prov: found a Prov_symbolic\"` (:390-394) on the same bytes")
    | .Prov_device => acc) []
  match xs with
  | [] => .NoTaint
  | _ => .NewTaint xs

/-- merge_taint — impl_mem.ml:966-974 (local to abst). -/
def mergeTaint : ProvTaint → ProvTaint → ProvTaint
  | .NoTaint, .NoTaint => .NoTaint
  | .NoTaint, .NewTaint xs => .NewTaint xs
  | .NewTaint xs, .NoTaint => .NewTaint xs
  | .NewTaint xs, .NewTaint ys => .NewTaint (xs ++ ys)

/-- mk_ival — impl_mem.ml:670-677: under any PNVI variant an integer value
    carries NO provenance (`IV (Prov_none, n)`); otherwise `IV (prov, n)`.
    Reads the switch set (`is_PNVI`, impl_mem.ml:662-668). At the default set
    it is `IV prov n` (`mkIval_default`). PNVI arc S2 (2026-10-07). -/
def mkIval [CerbGlobal.Switches] (prov : Provenance) (n : Int) : IntegerValue :=
  if CerbGlobal.is_PNVI () then .IV .Prov_none n else .IV prov n

theorem mkIval_default (prov : Provenance) (n : Int) :
    @mkIval ⟨[]⟩ prov n = .IV prov n := rfl

/-- The same two facts at the default-pinned wrappers' instance
    `⟨CerbGlobal.defaultSwitches⟩` (`reconstructValue(_lemFuel)`), stated for a
    consumer's `simp only` sets (no `@[simp]`: the global simp set is unchanged). -/
theorem mkIval_defaultSwitches (prov : Provenance) (n : Int) :
    @mkIval ⟨CerbGlobal.defaultSwitches⟩ prov n = .IV prov n := rfl

theorem is_PNVI_defaultSwitches : @CerbGlobal.is_PNVI ⟨CerbGlobal.defaultSwitches⟩ () = false := rfl

/-- find_overlaping — impl_mem.ml:795-875: the live allocations whose range
    contains `addr` (or, under AE_UDI, ends exactly at it), optionally only the
    EXPOSED ones; the first two found, in ascending allocation-id order.
    * The `(require_exposed, allow_one_past)` table, :799-813: the FIRST
      `SW_PNVI _` of the switch list (`Switches.has_switch_pred`,
      switches.ml:58-59 `List.find_opt`) — PLAIN `(false, false)`, AE
      `(true, false)`, AE_UDI `(true, true)`; no PNVI switch `(false, false)`.
      Its `Some _ -> assert false` arm (:810-811; the predicate admits only
      `SW_PNVI`, so unreachable by construction) is REFUSED (design §G.1 row
      R3, `R-PNVI-02`).
    * The fold, :814-875 (:843-874 is a commented-out older body): `IntMap.fold` visits keys in INCREASING order (OCaml
      `Map.S.fold`; `IntMap = Map.Make(Z)`, impl_mem.ml:93, `Z.compare`);
      `Std.TreeMap.foldl` visits `toList`, which is strictly ascending under
      `compare` on `Int` (`allocations_foldl_ascending` below) — the same
      order, so the `DoubleAlloc (first, second)` pair is the same pair
      (`resolveIota` tries `first` first, :928-937).
    * Candidate test, :815-831: not dead (`List.mem alloc_id
      st.dead_allocations`), `base ≤ addr < base + size`, then the exposure
      requirement; ELSE (dead, or out of range) under `allow_one_past`:
      `addr = base + size` and the exposure requirement (no dead check on this
      branch — mirrored as written).
    * A THIRD candidate (:839-842 `DoubleAlloc _, Some _ -> (* TODO: I guess
      there is an invariant that the new_alloc is either of the DoubleAlloc *)
      acc` — dropped silently upstream) is REFUSED (§G.1 row R4, `R-PNVI-03`;
      §H: the operator accepted the proposed refusal of `:840-842`).
    Called only under `is_PNVI` (abst's pointer arm here; ptrfromint's PNVI
    arm, PNVI arc S3): at the default set the result is never consulted. PNVI
    arc S2 (2026-10-07). -/
def findOverlapping [CerbGlobal.Switches] (st : MemState) (addr : Address) : OverlapResult :=
  let (requireExposed, allowOnePast) : Bool × Bool :=
    match CerbGlobal.Switches.switches.find? (fun | .PNVI _ => true | _ => false) with
    | some (.PNVI .PLAIN) => (false, false)
    | some (.PNVI .AE) => (true, false)
    | some (.PNVI .AE_UDI) => (true, true)
    | some _ =>
      failwithI (pnviRefusal "R-PNVI-02: find_overlaping, a non-PNVI switch matched the SW_PNVI predicate — impl_mem.ml:810-811 `Some _ -> assert false`")
    | none => (false, false)
  st.allocations.foldl (init := OverlapResult.NoAlloc) fun acc allocId alloc =>
    let notExposedButRequired := requireExposed && alloc.taint != .Exposed
    let newOpt : Option StorageInstanceId :=
      if !(st.deadAllocations.contains allocId) && alloc.base ≤ addr && addr < alloc.base + alloc.size then
        if notExposedButRequired then none else some allocId      -- :816-822 (PNVI-ae, PNVI-ae-udi)
      else if allowOnePast then
        if addr == alloc.base + alloc.size && !notExposedButRequired then some allocId  -- :823-829 (PNVI-ae-udi)
        else none
      else none
    match acc, newOpt with
    | _, none => acc                                                  -- :833-834
    | .NoAlloc, some allocId => .SingleAlloc allocId                  -- :835-836
    | .SingleAlloc allocId1, some allocId2 => .DoubleAlloc allocId1 allocId2  -- :837-838
    | .DoubleAlloc _ _, some _ =>
      failwithI (pnviRefusal "R-PNVI-03: find_overlaping, a third candidate allocation — impl_mem.ml:839-842 `DoubleAlloc _, Some _ -> (* TODO: I guess there is an invariant that the new_alloc is either of the DoubleAlloc *) acc` (upstream drops it silently)")

/-- The order argument for `findOverlapping` (OCaml `IntMap.fold` visits keys in
    increasing order): `Std.TreeMap.foldl` over the allocations is the fold
    over `toList`, and `toList` is strictly ascending in the allocation id. -/
theorem allocations_foldl_ascending {δ : Type} (st : MemState) (f : δ → Int → Allocation → δ) (init : δ) :
    st.allocations.foldl f init = st.allocations.toList.foldl (fun a b => f a b.1 b.2) init ∧
      st.allocations.toList.Pairwise (fun (a b : Int × Allocation) => compare a.1 b.1 = Ordering.lt) :=
  ⟨Std.TreeMap.foldl_eq_foldl_toList, Std.TreeMap.ordered_keys_toList⟩

/-- `findOverlapping` reads only the allocations and the dead list (PNVI arc S2 review
    fix F1): any record update of the other fields leaves the closure unchanged —
    `findOverlapping_congr rfl rfl : findOverlapping { s with lastUsed := u } =
    findOverlapping s` — so a proof that compares a memory operation on `s` and on an
    updated `s` can rewrite the closure instead of reducing it. -/
theorem findOverlapping_congr [CerbGlobal.Switches] {s t : MemState}
    (h1 : s.allocations = t.allocations) (h2 : s.deadAllocations = t.deadAllocations) :
    findOverlapping s = findOverlapping t := by
  unfold findOverlapping
  rw [h1, h2]

/-- The `last_used` instance of `findOverlapping_congr`, as a rewrite rule (PNVI arc S3). -/
theorem findOverlapping_lastUsed [CerbGlobal.Switches] (s : MemState) (u : Option StorageInstanceId) :
    findOverlapping { s with lastUsed := u } = findOverlapping s := rfl

/-- An unspecified padding byte — OCaml's `padding_byte` / `AbsByte.v
    Prov_none None` (impl_mem.ml:1202; zero-discrepancy Z-23 re-cite). -/
-- NOTE (arc-7 S5a): the byte/allocation helpers below were `private`;
-- they were made public so equation lemmas could unfold them by name
-- (the reasoning-era consumers are parked: tag
-- park/reasoning-era-20260831). Kept public — no behavior change, and
-- downstream verification layers consume this module by name.
def paddingByte : AbsByte :=
  { prov := .Prov_none, copyOffset := none, value := none }

/-- The funptrmap: function-pointer address (= the function symbol's
    nat) ↦ (file digest, name). Field of mem_state — impl_mem.ml:489. -/
abbrev Funptrmap := List (Int × (String × String))

/-- Serialize a MemValue to bytes — repr, impl_mem.ml:1139-1220.
    Threads the funptrmap exactly like OCaml's
    `repr funptrmap mval : (funptrmap' × bytes)` — storing a PVfunction
    registers the symbol in the map (impl_mem.ml:1168-1185, survey
    finding 20); all other arms pass it through. -/
def memValueToBytes_lemFuel (lemFuel : Nat) (enumDefs : EnumDefs) (ambient : TagDefs) (funptrmap : Funptrmap)
    (val_ : MemValue) : Funptrmap × List AbsByte :=
  match lemFuel with
  | 0 => fuelExhaustedWith "CerbMem.memValueToBytes: fuel exhausted" (funptrmap, [])
  | lemFuel + 1 =>
  match val_ with
  | .MVunspecified ty =>
    -- impl_mem.ml:1142-1144
    let sz := sizeofCtype enumDefs ambient ty
    (funptrmap, List.replicate sz paddingByte)
  | .MVinteger ity (.IV prov n) =>
    -- impl_mem.ml:1145-1150 (size = sizeof (Basic (Integer ity)));
    -- `List.map (AbsByte.v prov)` — AbsByte.v's copy_offset DEFAULTS to
    -- None (impl_mem.ml:422-423): integer bytes carry NO copy_offset
    -- (audit-2 F8; previously `some i` here, which only pointer bytes
    -- get, impl_mem.ml:1186-1191)
    let sz := match CerberusImpl.sizeof_ity (CerberusImpl.resolveEnum enumDefs ity) with
      | some n => n
      | none => failwithI "CerbMem.memValueToBytes: the concrete memory model requires a complete implementation sizeof INTEGER"
    -- :1147 `AilTypesAux.is_signed_ity ity` = `Implementation.is_signed_ity`
    -- (ailTypesAux.lem:28) = the CerberusImpl mirror
    let rawBytes := intToBytes (CerberusImpl.is_signed_ity (CerberusImpl.resolveEnum enumDefs ity)) n sz
    (funptrmap, rawBytes.map fun v =>
      { prov := prov, copyOffset := none, value := v })
  | .MVfloating fty fv =>
    -- impl_mem.ml:1151-1156: Int64.bits_of_float over sizeof(fty) bytes
    -- (= 8 for all real floating types, DefaultImpl 8/8/8 hack — see
    -- CerberusImpl.sizeof_fty)
    let sz := match CerberusImpl.sizeof_fty fty with
      | some n => n
      | none => failwithI "CerbMem.memValueToBytes: the concrete memory model requires a complete implementation sizeof FLOAT"
    -- :1153-1155 `bytes_of_int true 8 (Z.of_int64 (Int64.bits_of_float fval))`:
    -- the SIGNED int64 reading of the bit pattern (so the assert's range
    -- is [-2^63, 2^63-1]); the bytes are the same two's complement
    -- named-deviation register N2 (VALIDATION.md §2b): Lean's Float.toBits
    -- canonicalizes every NaN to 0x7ff8000000000000, so a stored NaN loses
    -- the sign and payload that Int64.bits_of_float keeps (impl_mem.ml:1190).
    let bits : Int := fv.toBits.toInt64.toInt
    let rawBytes := intToBytes true bits sz
    (funptrmap, rawBytes.map fun v => { prov := .Prov_none, copyOffset := none, value := v })
  | .MVpointer _ (.PV prov base) =>
    -- impl_mem.ml:1157-1192
    match base with
    | .PVnull _ =>
      -- impl_mem.ml:1165-1167: all-zero bytes, Prov_none, NO copy_offset
      let rawBytes := intToBytes false 0 targetPtrSize
      (funptrmap, rawBytes.map fun v =>
        { prov := .Prov_none, copyOffset := none, value := v })
    | .PVfunction (Symbol fileDig n optName) =>
      -- impl_mem.ml:1168-1185: bytes are the SYMBOL's nat (previously 0
      -- here — the finding-20 bug); an SD_Id symbol is registered in the
      -- funptrmap; bytes carry prov, NO copy_offset (List.map (AbsByte.v
      -- prov), impl_mem.ml:1181-1185)
      let funptrmap' := match optName with
        | SD_Id name =>
          ((n : Int), (fileDig, name)) ::
            funptrmap.filter (fun (a, _) => a != (n : Int))  -- IntMap.add = replace-or-insert
        | _ => funptrmap
      -- named-deviation register N1 (VALIDATION.md §2b): `n` is the symbol's
      -- fresh-supply number, which the oracle numbers differently; its bytes,
      -- `%p` and integer value (`intfromptr`) are a registered difference.
      let rawBytes := intToBytes false n targetPtrSize   -- :1183 `bytes_of_int false`
      (funptrmap', rawBytes.map fun v =>
        { prov := prov, copyOffset := none, value := v })
    | .PVconcrete _ addr =>
      -- impl_mem.ml:1186-1191: bytes carry prov AND copy_offset
      let rawBytes := intToBytes false addr targetPtrSize   -- :1189 "we model address as unsigned"
      (funptrmap, (rawBytes.zip (List.range rawBytes.length)).map fun (v, i) =>
        { prov := prov, copyOffset := some i, value := v })
  | .MVarray elems =>
    -- impl_mem.ml:1193-1200: fold threading funptrmap, concat of reprs
    let (fpm, bss) := elems.foldl (init := (funptrmap, ([] : List (List AbsByte))))
      fun (acc : Funptrmap × List (List AbsByte)) mval =>
        let (fpm, bss) := acc
        let (fpm', bs) := memValueToBytes_lemFuel lemFuel enumDefs ambient fpm mval
        (fpm', bs :: bss)
    (fpm, bss.reverse.flatten)
  | .MVstruct tagSym members =>
    -- impl_mem.ml:1202-1214: pad from the previous member's end up to
    -- each member's offsetsof offset (unspecified bytes), then the
    -- member's bytes; then trailing padding out to sizeof(struct).
    let (offs, lastOff) := offsetsof enumDefs ambient ambient tagSym (ignoreFlexible := true)
    let finalPad := sizeofCtype enumDefs ambient (mkCtype (.Struct tagSym)) - lastOff  -- impl_mem.ml:1205
    -- fold2 over layout and members (impl_mem.ml:1207-1212); lengths
    -- coincide for well-typed values (OCaml fold_left2 would raise
    -- Invalid_argument otherwise — zip truncates instead).
    -- DOCUMENTED DIVERGENCE (mem-scale C3, 2026-09-02): the OCaml
    -- accumulates `acc @ List.init pad padding_byte @ bs` inside the
    -- left fold (impl_mem.ml:1211) — a List.append of the growing
    -- accumulator per member, quadratic in members × bytes; we instead
    -- cons each member's chunk (padding ++ bytes) onto a REVERSED chunk
    -- list and flatten once at the end (linear). Same result list:
    -- `memValueToBytes_lemFuel_eq_append` below is the kernel-checked
    -- equality with the append-accumulating reference form
    -- (`memValueToBytes_append_lemFuel`, the pre-C3 text).
    let (fpm, _, revChunks) := (offs.zip members).foldl
      (init := (funptrmap, (0 : Nat), ([] : List (List AbsByte))))
      fun (acc : Funptrmap × Nat × List (List AbsByte))
          (p : (identifier × ctype × Nat) × (identifier × ctype × MemValue)) =>
        let (fpm, lastOff, revChunks) := acc
        let ((_, ty, off), (_, _, mval)) := p
        let pad := off - lastOff
        let (fpm', bs) := memValueToBytes_lemFuel lemFuel enumDefs ambient fpm mval
        (fpm', off + sizeofCtype enumDefs ambient ty, (List.replicate pad paddingByte ++ bs) :: revChunks)
    (fpm, revChunks.reverse.flatten ++ List.replicate finalPad paddingByte)  -- impl_mem.ml:1214
  | .MVunion tagSym _ mval =>
    -- impl_mem.ml:1216-1219: the active member's bytes, padded out with
    -- unspecified bytes to sizeof(union).
    let size := sizeofCtype enumDefs ambient (mkCtype (.Union0 tagSym))
    let (fpm, bs) := memValueToBytes_lemFuel lemFuel enumDefs ambient funptrmap mval
    (fpm, bs ++ List.replicate (size - bs.length) paddingByte)

/-- MEASURED wrapper (fuel-parameter arc C2, 2026-09-04): the worker's own
    counter starts from the structural size of the value it recurses on
    (`memValueSize val_`: MVarray/MVstruct/MVunion descend into components) —
    the hand-written twin of a `declare {lean} fuel_measure`; the sufficiency
    theorem `memValueToBytes_measure_sufficient` is in
    CerbMem_lemMeasureProofs.lean. Its `[LemFuel]` binder (C2: "for the
    ambient layout oracle") went at C4: the layout oracle is measured. -/
def memValueToBytes (enumDefs : EnumDefs) (ambient : TagDefs) (funptrmap : Funptrmap) (val_ : MemValue) :
    Funptrmap × List AbsByte :=
  memValueToBytes_lemFuel (memValueSize val_) enumDefs ambient funptrmap val_

/-! ### C3 reference form + equality theorem (mem-scale S1, 2026-09-02)

`memValueToBytes_append_lemFuel` is the PRE-C3 text of
`memValueToBytes_lemFuel` verbatim (only the name and the recursive
calls renamed): the struct arm accumulates with `accBs ++ pad ++ bs`
inside the left fold, mirroring `impl_mem.ml:1207-1212` shape-for-shape.
It is NOT executed by the driver; it exists so the divergence is a
kernel-checked equality (`memValueToBytes_lemFuel_eq_append`) rather
than a claim. Charter §1 carve-out [R1/F5]. -/

/-- Reference form (pre-C3): append-accumulating struct arm. -/
def memValueToBytes_append_lemFuel (lemFuel : Nat) (enumDefs : EnumDefs) (ambient : TagDefs) (funptrmap : Funptrmap)
    (val_ : MemValue) : Funptrmap × List AbsByte :=
  match lemFuel with
  | 0 => fuelExhaustedWith "CerbMem.memValueToBytes: fuel exhausted" (funptrmap, [])
  | lemFuel + 1 =>
  match val_ with
  | .MVunspecified ty =>
    let sz := sizeofCtype enumDefs ambient ty
    (funptrmap, List.replicate sz paddingByte)
  | .MVinteger ity (.IV prov n) =>
    let sz := match CerberusImpl.sizeof_ity (CerberusImpl.resolveEnum enumDefs ity) with
      | some n => n
      | none => failwithI "CerbMem.memValueToBytes: the concrete memory model requires a complete implementation sizeof INTEGER"
    -- :1147 `AilTypesAux.is_signed_ity ity` = `Implementation.is_signed_ity`
    -- (ailTypesAux.lem:28) = the CerberusImpl mirror
    let rawBytes := intToBytes (CerberusImpl.is_signed_ity (CerberusImpl.resolveEnum enumDefs ity)) n sz
    (funptrmap, rawBytes.map fun v =>
      { prov := prov, copyOffset := none, value := v })
  | .MVfloating fty fv =>
    let sz := match CerberusImpl.sizeof_fty fty with
      | some n => n
      | none => failwithI "CerbMem.memValueToBytes: the concrete memory model requires a complete implementation sizeof FLOAT"
    -- :1153-1155 `bytes_of_int true 8 (Z.of_int64 (Int64.bits_of_float fval))`:
    -- the SIGNED int64 reading of the bit pattern (so the assert's range
    -- is [-2^63, 2^63-1]); the bytes are the same two's complement
    -- named-deviation register N2 (VALIDATION.md §2b): Lean's Float.toBits
    -- canonicalizes every NaN to 0x7ff8000000000000, so a stored NaN loses
    -- the sign and payload that Int64.bits_of_float keeps (impl_mem.ml:1190).
    let bits : Int := fv.toBits.toInt64.toInt
    let rawBytes := intToBytes true bits sz
    (funptrmap, rawBytes.map fun v => { prov := .Prov_none, copyOffset := none, value := v })
  | .MVpointer _ (.PV prov base) =>
    match base with
    | .PVnull _ =>
      let rawBytes := intToBytes false 0 targetPtrSize
      (funptrmap, rawBytes.map fun v =>
        { prov := .Prov_none, copyOffset := none, value := v })
    | .PVfunction (Symbol fileDig n optName) =>
      let funptrmap' := match optName with
        | SD_Id name =>
          ((n : Int), (fileDig, name)) ::
            funptrmap.filter (fun (a, _) => a != (n : Int))
        | _ => funptrmap
      -- named-deviation register N1 (VALIDATION.md §2b): `n` is the symbol's
      -- fresh-supply number, which the oracle numbers differently; its bytes,
      -- `%p` and integer value (`intfromptr`) are a registered difference.
      let rawBytes := intToBytes false n targetPtrSize   -- :1183 `bytes_of_int false`
      (funptrmap', rawBytes.map fun v =>
        { prov := prov, copyOffset := none, value := v })
    | .PVconcrete _ addr =>
      let rawBytes := intToBytes false addr targetPtrSize   -- :1189 "we model address as unsigned"
      (funptrmap, (rawBytes.zip (List.range rawBytes.length)).map fun (v, i) =>
        { prov := prov, copyOffset := some i, value := v })
  | .MVarray elems =>
    let (fpm, bss) := elems.foldl (init := (funptrmap, ([] : List (List AbsByte))))
      fun (acc : Funptrmap × List (List AbsByte)) mval =>
        let (fpm, bss) := acc
        let (fpm', bs) := memValueToBytes_append_lemFuel lemFuel enumDefs ambient fpm mval
        (fpm', bs :: bss)
    (fpm, bss.reverse.flatten)
  | .MVstruct tagSym members =>
    let (offs, lastOff) := offsetsof enumDefs ambient ambient tagSym (ignoreFlexible := true)
    let finalPad := sizeofCtype enumDefs ambient (mkCtype (.Struct tagSym)) - lastOff
    let (fpm, _, bs) := (offs.zip members).foldl
      (init := (funptrmap, (0 : Nat), ([] : List AbsByte)))
      fun (acc : Funptrmap × Nat × List AbsByte)
          (p : (identifier × ctype × Nat) × (identifier × ctype × MemValue)) =>
        let (fpm, lastOff, accBs) := acc
        let ((_, ty, off), (_, _, mval)) := p
        let pad := off - lastOff
        let (fpm', bs) := memValueToBytes_append_lemFuel lemFuel enumDefs ambient fpm mval
        (fpm', off + sizeofCtype enumDefs ambient ty, accBs ++ List.replicate pad paddingByte ++ bs)
    (fpm, bs ++ List.replicate finalPad paddingByte)
  | .MVunion tagSym _ mval =>
    let size := sizeofCtype enumDefs ambient (mkCtype (.Union0 tagSym))
    let (fpm, bs) := memValueToBytes_append_lemFuel lemFuel enumDefs ambient funptrmap mval
    (fpm, bs ++ List.replicate (size - bs.length) paddingByte)

/-- The list fact behind C3: a left fold that APPENDS each step's chunk to
    the accumulator (third component) equals the fold that CONSES the
    chunks and flattens the reversed list at the end. Stated over the
    exact accumulator shape of the struct arm (`γ × Nat × List α`, the
    funptrmap × running offset × bytes triple) and an arbitrary per-step
    function `step`, generalised over the starting chunk list. -/
theorem foldl_append_eq_flatten_reverse_aux {γ β α : Type}
    (step : γ → Nat → β → γ × Nat × List α) (l : List β) (g : γ) (n : Nat)
    (acc : List (List α)) :
    l.foldl (fun (p : γ × Nat × List α) b =>
        ((step p.1 p.2.1 b).1, (step p.1 p.2.1 b).2.1, p.2.2 ++ (step p.1 p.2.1 b).2.2))
      (g, n, acc.reverse.flatten) =
    ((l.foldl (fun (p : γ × Nat × List (List α)) b =>
        ((step p.1 p.2.1 b).1, (step p.1 p.2.1 b).2.1, (step p.1 p.2.1 b).2.2 :: p.2.2)) (g, n, acc)).1,
     (l.foldl (fun (p : γ × Nat × List (List α)) b =>
        ((step p.1 p.2.1 b).1, (step p.1 p.2.1 b).2.1, (step p.1 p.2.1 b).2.2 :: p.2.2)) (g, n, acc)).2.1,
     (l.foldl (fun (p : γ × Nat × List (List α)) b =>
        ((step p.1 p.2.1 b).1, (step p.1 p.2.1 b).2.1, (step p.1 p.2.1 b).2.2 :: p.2.2)) (g, n, acc)).2.2.reverse.flatten) := by
  induction l generalizing g n acc with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldl_cons]
    have h : acc.reverse.flatten ++ (step g n b).2.2 = ((step g n b).2.2 :: acc).reverse.flatten := by
      simp [List.reverse_cons, List.flatten_append]
    rw [h]
    exact ih _ _ _

/-- Starting-from-empty instance of the aux lemma (`[] = [].reverse.flatten`). -/
theorem foldl_append_eq_flatten_reverse {γ β α : Type}
    (step : γ → Nat → β → γ × Nat × List α) (l : List β) (g : γ) (n : Nat) :
    l.foldl (fun (p : γ × Nat × List α) b =>
        ((step p.1 p.2.1 b).1, (step p.1 p.2.1 b).2.1, p.2.2 ++ (step p.1 p.2.1 b).2.2))
      (g, n, []) =
    ((l.foldl (fun (p : γ × Nat × List (List α)) b =>
        ((step p.1 p.2.1 b).1, (step p.1 p.2.1 b).2.1, (step p.1 p.2.1 b).2.2 :: p.2.2)) (g, n, [])).1,
     (l.foldl (fun (p : γ × Nat × List (List α)) b =>
        ((step p.1 p.2.1 b).1, (step p.1 p.2.1 b).2.1, (step p.1 p.2.1 b).2.2 :: p.2.2)) (g, n, [])).2.1,
     (l.foldl (fun (p : γ × Nat × List (List α)) b =>
        ((step p.1 p.2.1 b).1, (step p.1 p.2.1 b).2.1, (step p.1 p.2.1 b).2.2 :: p.2.2)) (g, n, [])).2.2.reverse.flatten) :=
  foldl_append_eq_flatten_reverse_aux step l g n []

/-- C3 equality: the linear serialisation equals the append-accumulating
    reference form at every fuel, on every input. Induction on fuel; every
    arm but the struct arm is textually identical once the recursive calls
    are rewritten by the induction hypothesis; the struct arm is
    `foldl_append_eq_flatten_reverse`. -/
theorem memValueToBytes_lemFuel_eq_append :
    ∀ (lemFuel : Nat) (enumDefs : EnumDefs) (ambient : TagDefs) (funptrmap : Funptrmap) (val_ : MemValue),
      memValueToBytes_lemFuel lemFuel enumDefs ambient funptrmap val_ =
        memValueToBytes_append_lemFuel lemFuel enumDefs ambient funptrmap val_ := by
  intro lemFuel
  induction lemFuel with
  | zero => intros; rfl
  | succ lemFuel ih =>
    intro enumDefs ambient funptrmap val_
    have hf : memValueToBytes_lemFuel lemFuel = memValueToBytes_append_lemFuel lemFuel := by
      funext e a f v; exact ih e a f v
    unfold memValueToBytes_lemFuel memValueToBytes_append_lemFuel
    rw [hf]
    cases val_ with
    | MVstruct tagSym members =>
      dsimp only
      -- `++` is left-associative: the reference arm is `(accBs ++ pad) ++ bs`;
      -- re-associate so the step's chunk is `pad ++ bs`, then `step` in
      -- projection form (the shape `dsimp` leaves the two folds in):
      -- funptrmap' , next running offset , this member's chunk.
      simp only [List.append_assoc]
      rw [foldl_append_eq_flatten_reverse
        (step := fun (fpm : Funptrmap) (lastOff : Nat)
            (p : (identifier × ctype × Nat) × (identifier × ctype × MemValue)) =>
          ((memValueToBytes_append_lemFuel lemFuel enumDefs ambient fpm p.2.2.2).1,
           p.1.2.2 + sizeofCtype enumDefs ambient p.1.2.1,
           List.replicate (p.1.2.2 - lastOff) paddingByte ++
             (memValueToBytes_append_lemFuel lemFuel enumDefs ambient fpm p.2.2.2).2))]
    | _ => rfl

theorem memValueToBytes_eq_append (enumDefs : EnumDefs) (ambient : TagDefs) (funptrmap : Funptrmap) (val_ : MemValue) :
    memValueToBytes enumDefs ambient funptrmap val_ =
      memValueToBytes_append_lemFuel (memValueSize val_) enumDefs ambient funptrmap val_ :=
  memValueToBytes_lemFuel_eq_append (memValueSize val_) enumDefs ambient funptrmap val_

/-- `chunksOf e n l`: the `n` successive `e`-element slices of `l`
    (consume-and-return-rest; a slice past the end is short/empty, as
    `take`/`drop` are). One pass, linear in `e * n`. -/
def chunksOf (e : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | n + 1, l => l.take e :: chunksOf e n (l.drop e)

/-- Each chunk is the corresponding index-slice: `chunksOf` computes exactly
    the per-element slices `(l.drop (i*e)).take e` for `i < n`. -/
theorem chunksOf_eq_range_map (e n : Nat) (l : List α) :
    chunksOf e n l = (List.range n).map fun i => (l.drop (i * e)).take e := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [chunksOf, ih, Nat.zero_mul, List.drop_zero, Function.comp_def, List.drop_drop,
      Nat.succ_mul, Nat.add_comm]

/-- Reconstruct a MemValue from bytes — `abst`, impl_mem.ml:945-1128, with
    OCaml's full interface (PNVI arc S2, 2026-10-07): the switch set (the
    `is_PNVI` reads of `mk_ival`, :670-677, and of the pointer arm, :1057),
    the `find_overlaping` CLOSURE (`abst find_overlaping …`, :951 — every
    caller passes `find_overlaping st`, :1263/:1488/:1600; here `loadM` passes
    `findOverlapping st`), and the provenance TAINT as the first component of
    the result (`provs_of_bytes` at the integer/byte leaves, merged by
    `mergeTaint` in the array/struct folds in OCaml's argument order —
    `merge_taint taint taint_acc`, :1027/:1104, defined :967-975 — `NoTaint`
    elsewhere).
    INVARIANT (differs from OCaml's consume-and-return-rest shape at the
    LEAVES): `bytes` is exactly the sizeof(ty) slice for this value; the
    array arm hands each element exactly its slice in one linear pass
    (C1, see the arm), the struct/union arms re-slice per member.
    `unionmap` is mem_state.last_used_union_members and
    `addr` the value's address — consulted ONLY by the Union arm
    (impl_mem.ml:1108-1128); `funptrmap` is mem_state.funptrmap —
    consulted ONLY by the Pointer-to-Function arm (impl_mem.ml:1037-1050)
    — exactly as in OCaml's abst.
    FAILURE LEAVES carry an explicit `NoTaint` beside the failing value
    (`(.NoTaint, failwithI …)`): OCaml's exception aborts the whole `abst`;
    the strict pair evaluates the failing component and aborts the same way
    (the run requires LEAN_ABORT_ON_PANIC); the shape keeps the wrapper
    `reconstructValue_lemFuel` (the `.2` projection) kernel-equal to the
    pre-S2 text, whose leaves are the bare `failwithI` (`failwithI` is opaque —
    a projection of a failing pair is not provably the failing component).
    Not ported: is_zap (a refused switch's caller, :1488).
    The DEFAULT-MODE consumer is the wrapper `reconstructValue(_lemFuel)` below,
    pinned at `⟨CerbGlobal.defaultSwitches⟩`; production (`loadM`) calls THIS
    function with the ambient instance. -/
def reconstructValueAbst_lemFuel [CerbGlobal.Switches] (lemFuel : Nat) (enumDefs : EnumDefs) (ambient : TagDefs)
    (findOverlapping : Address → OverlapResult)
    (unionmap : List (Int × identifier))
    (funptrmap : Funptrmap) (addr : Int)
    (ty : ctype) (bytes : List AbsByte) : ProvTaint × MemValue :=
  match lemFuel with
  | 0 => (.NoTaint, fuelExhaustedWith "CerbMem.reconstructValue: fuel exhausted" (.MVunspecified ty))
  | lemFuel + 1 =>
  match ty with
  | Ctype _ (.Basic (.Integer ity)) =>
    -- impl_mem.ml:984-995 (signedness via the implementation, as
    -- AilTypesAux.is_signed_ity does there); provenance via the INTEGER
    -- policy — pvi_split_bytes' combine_prov fold (:986, :455-460); the
    -- taint is provs_of_bytes of the same bytes (:988, :462-479); the value
    -- through mk_ival (:992, :670-677).
    let signed := CerberusImpl.is_signed_ity (CerberusImpl.resolveEnum enumDefs ity)
    let prov := provFromIntegerBytes bytes
    (provsOfBytes bytes,
      match bytesToInt bytes signed with
      | some n => .MVinteger ity (mkIval prov n)
      | none => .MVunspecified ty)
  | Ctype _ (.Basic (.Floating fty)) =>
    -- impl_mem.ml:1009-1020 ("we don't care about provenances for floats": NoTaint)
    (.NoTaint,
      match bytesToInt bytes false with
      | some n =>
        let bits : UInt64 := n.toNat.toUInt64
        .MVfloating fty (Float.ofBits bits)
      | none => .MVunspecified ty)
  | Ctype _ (.Pointer _ pointeeCty) =>
    -- impl_mem.ml:1030-1093; the taint is `NoTaint (* PNVI-ae-udi *)`
    -- (:1034), the first component OUTSIDE the match, as in OCaml (so the
    -- unknown-function-pointer failure below is a bare leaf of the value). MVpointer stores the POINTEE type: every OCaml arm builds
    -- `MVpointer (ref_ty, ...)` — matching `typeof` (MVpointer (ref_ty, _) →
    -- Pointer (no_qualifiers, ref_ty)) and our own pointerMval/MVpointer.refTy.
    -- (Audit-2 C1: this previously stored the full pointer type `ty` — one
    -- indirection too many.) Provenance via the POINTER policy —
    -- AbsByte.split_bytes (:1033, :432-453).
    (.NoTaint,
    match bytesToInt bytes false with
    | some 0 =>
      -- both the Function and the object branch map 0 to PVnull
      -- (impl_mem.ml:1040-1042, :1052-1054)
      .MVpointer pointeeCty (.PV .Prov_none (.PVnull pointeeCty))
    | some ptrAddr =>
      let (prov, validPtrProv) := splitBytesProv bytes
      match pointeeCty with
      | Ctype _ (.Function _ _ _) =>
        -- impl_mem.ml:1039-1050: a pointer-to-function is rebuilt from
        -- the funptrmap entry registered at store time (repr); the address IS
        -- the function symbol's nat. Unknown address: OCaml failwith — panic.
        -- (OCaml's own FIXME about same-id symbols across files, :1044,
        -- applies unchanged.)
        match funptrmap.find? (fun (a, _) => a == ptrAddr) with
        | some (_, (fileDig, name)) =>
          .MVpointer pointeeCty (.PV prov (.PVfunction (Symbol fileDig ptrAddr.toNat (SD_Id name))))
        | none => failwithI s!"CerbMem.reconstructValue: unknown function pointer: {ptrAddr}"
      | _ =>
        -- impl_mem.ml:1051-1090: under is_PNVI (:1057), a pointer whose bytes are not
        -- one whole-pointer copy (`NotValidPtrProv`) takes its provenance from
        -- find_overlaping at its address (`NoAlloc → Prov_none`, `SingleAlloc →
        -- Prov_some`); `ValidPtrProv → prov`; otherwise (`else prov`, :1087-1088)
        -- the shared provenance. The `DoubleAlloc` arm (:1079-1082, `(* FIXME/
        -- HACK(VICTOR): This is wrong, but when serialising the memory in the UI,
        -- I get this failwith. *) Prov_some alloc_id1`) is REFUSED (design §G.1
        -- row R6, class (C): upstream says "This is wrong"; `R-PNVI-05`). At the
        -- default switch set `is_PNVI () = false` and `findOverlapping` is never
        -- consulted (`reconstructValue_lemFuel_eq_legacy`, the test module).
        let prov :=
          if CerbGlobal.is_PNVI () then
            if validPtrProv then prov
            else match findOverlapping ptrAddr with
              | .NoAlloc => .Prov_none
              | .SingleAlloc allocId => .Prov_some allocId
              | .DoubleAlloc _ _ =>
                failwithI (pnviRefusal "R-PNVI-05: abst, pointer arm, NotValidPtrProv, DoubleAlloc — impl_mem.ml:1079-1082 `(* FIXME/HACK(VICTOR): This is wrong, but when serialising the memory in the UI, I get this failwith. *) Prov_some alloc_id1`")
          else prov
        .MVpointer pointeeCty (.PV prov (.PVconcrete none ptrAddr.toNat))
    | none =>
      -- impl_mem.ml:1091-1092 `MVunspecified (Ctype ([], Pointer (no_qualifiers,
      -- ref_ty)))`: the pointee QUALIFIERS are dropped (zero-discrepancy
      -- Z-19: this kept `ty` verbatim; the ctype text is a verdict value
      -- wherever an unspecified pointer is printed)
      .MVunspecified (Ctype [] (.Pointer no_qualifiers pointeeCty)))
  | Ctype _ (.Array0 elemCty (some n)) =>
    -- impl_mem.ml:1021-1028; NOTE OCaml's `self elem_ty cs` does NOT
    -- advance ~addr per element — every element sees the array's addr
    -- (mirrored: nested-union lookups use the array base address).
    -- The taint: `aux` folds `merge_taint taint taint_acc` from `NoTaint`
    -- over the elements in order (:1022-1028) — the foldl below.
    -- SHAPE (mem-scale C1, 2026-09-02): ONE consume-and-return-rest pass
    -- over the bytes (`chunksOf`: take elemSize, recurse on the rest),
    -- which is the OCaml `aux`'s shape (`self elem_ty cs` returns the
    -- unconsumed suffix `cs'`), minus the OCaml's per-call guard `if
    -- List.length bs < sizeof cty then failwith` (:964-965) — DELIBERATELY
    -- NOT MIRRORED: that guard re-walks the remaining list on every
    -- recursive call and is what makes the oracle quadratic in the element
    -- count on aggregate loads (upstream-tray item). The pre-C1 Lean text
    -- re-sliced from the array's start per element (`bytes.drop
    -- (i*elemSize) |>.take elemSize`), also quadratic; the kernel-checked
    -- equality with that reference form is `reconstructValueLegacy_lemFuel_eq_indexed`
    -- (test/Unit/ReconstructLegacyTest.lean, retired there in PNVI arc S2).
    -- Linear in |bytes|.
    -- Zero-discrepancy Z-18: no zero-sized-element short-circuit — OCaml's
    -- `aux (Z.to_int n)` builds n elements whatever sizeof elem_ty is;
    -- `chunksOf 0 n` yields n empty slices, the same shape.
    -- (A zero-sized element type is anyway rejected by the shared front
    -- end: tests/z2-probes/mem/empty_struct.c is UB061 on all engines.)
    let nNat := n.toNat
    let elemSize := sizeofCtype enumDefs ambient elemCty
    let rs := (chunksOf elemSize nNat bytes).map fun elemBytes =>
        reconstructValueAbst_lemFuel lemFuel enumDefs ambient findOverlapping unionmap funptrmap addr elemCty elemBytes
    (rs.foldl (fun taintAcc r => mergeTaint r.1 taintAcc) .NoTaint, .MVarray (rs.map Prod.snd))
  | Ctype _ (.Atomic innerCty) =>
    -- impl_mem.ml:1094-1096 (same repr as the non-atomic version)
    reconstructValueAbst_lemFuel lemFuel enumDefs ambient findOverlapping unionmap funptrmap addr innerCty bytes
  | Ctype _ .Byte =>
    -- impl_mem.ml:996-1008 ("handled similarly to integers": provenance
    -- via pvi_split_bytes' combine_prov fold, :999; taint provs_of_bytes, :1001;
    -- mk_ival, :1005)
    let prov := provFromIntegerBytes (bytes.take 1)
    (provsOfBytes (bytes.take 1),
      match bytesToInt (bytes.take 1) false with
      | some n => .MVinteger .Char0 (mkIval prov n)
      | none => .MVunspecified ty)
  | Ctype _ (.Struct tagSym) =>
    -- impl_mem.ml:1097-1107: member-wise reconstruct at the offsetsof
    -- offsets (ignore_flexible=true), skipping inter-member padding; the
    -- taint folds `merge_taint taint taint_acc` from `NoTaint` (:1100-1105).
    -- NOTE OCaml's `self ~offset:pad` advances the member addr by the
    -- PADDING before the member only, not by the member offset
    -- (:1102-1103) — mirrored quirk; addr is only consulted by nested union
    -- lookups.
    -- An UNKNOWN tag is OCaml's `Pmap.find` Not_found inside `sizeof cty`
    -- (:1099) / `offsetsof` (:1105): the exception escapes and nothing of
    -- the struct is computed — so the leaf is the WHOLE result here, and
    -- the fold runs only once the tag is known to resolve (hotfix
    -- fix/fuel-forms-carriers option (d), 2026-09-20 — record
    -- docs/2026-09-20_fuel-forms-carriers-hotfix-record.md §3.5: the
    -- former shape folded over the failure value's projection
    -- `(failwithI …).fst`, a fail-open-shaped remnant; the row-6 measure
    -- proof needs no equation about the opaque leaf). `offsetsof`'s own
    -- leaf is untouched; the message differs from the oracle's exception
    -- text (failure TEXT is an allowed discrepancy class).
    match CerbTagsWf.lookupEntry ambient tagSym with
    | none => (.NoTaint, failwithI "CerbMem.reconstructValue: unknown struct tag (OCaml: Pmap.find Not_found in sizeof/offsetsof, impl_mem.ml:1067/1073)")
    | some _ =>
      let (offs, _) := offsetsof enumDefs ambient ambient tagSym (ignoreFlexible := true)
      let res := offs.foldl
        (init := (ProvTaint.NoTaint, ([] : List (identifier × ctype × MemValue)), (0 : Nat)))
        fun (acc : ProvTaint × List (identifier × ctype × MemValue) × Nat) (memb : identifier × ctype × Nat) =>
          let (ident, membTy, off) := memb
          let pad := off - acc.2.2
          let membBytes := bytes.drop off |>.take (sizeofCtype enumDefs ambient membTy)
          let r := reconstructValueAbst_lemFuel lemFuel enumDefs ambient findOverlapping unionmap funptrmap (addr + (pad : Int)) membTy membBytes
          (mergeTaint r.1 acc.1, (ident, membTy, r.2) :: acc.2.1, off + sizeofCtype enumDefs ambient membTy)
      (res.1, .MVstruct tagSym res.2.1.reverse)
  | Ctype _ (.Union0 tagSym) =>
    -- impl_mem.ml:1108-1128: select the member recorded in
    -- last_used_union_members at this address; default to the FIRST
    -- declared member when absent (:1116-1118); the taint is the member's
    -- (:1125-1126). (`is_zap`, :1110-1112, is not ported.)
    match CerbTagsWf.lookupEntry ambient tagSym with
    | some (_, (_, UnionDef membrs)) =>
      match membrs with
      | [] => (.NoTaint, failwithI "CerbMem.reconstructValue: empty UnionDef (OCaml: match failure)")
      | (firstIdent, (_, _, _, firstTy)) :: _ =>
        -- ident comparison is by NAME (idEqual), as OCaml's
        -- Eq Symbol.identifier instance does (:1120). A recorded identifier
        -- that names no member is OCaml's `assert false` (:1121-1122): the
        -- exception escapes, no member is reconstructed — so the leaf is the
        -- WHOLE result (hotfix fix/fuel-forms-carriers option (d),
        -- 2026-09-20, record §3.5; the former shape recursed on the failure
        -- value's `.snd`). The member is selected BEFORE the recursion; the
        -- recursive call is `self membr_ty bs1` (:1125), the result `MVunion`
        -- (:1126).
        match unionmap.find? (fun (a, _) => a == addr) with
        | none =>
          let r := reconstructValueAbst_lemFuel lemFuel enumDefs ambient findOverlapping unionmap funptrmap addr firstTy
              (bytes.take (sizeofCtype enumDefs ambient firstTy))
          (r.1, .MVunion tagSym firstIdent r.2)
        | some (_, membr) =>
          match membrs.find? (fun (i, _) => idEqual i membr) with
          | some (membIdent, (_, _, _, membTy)) =>
            let r := reconstructValueAbst_lemFuel lemFuel enumDefs ambient findOverlapping unionmap funptrmap addr membTy
                (bytes.take (sizeofCtype enumDefs ambient membTy))
            (r.1, .MVunion tagSym membIdent r.2)
          | none => (.NoTaint, failwithI "CerbMem.reconstructValue: recorded union member not in UnionDef (OCaml: assert false)")
    | _ => (.NoTaint, failwithI "CerbMem.reconstructValue: Union tag not a UnionDef (OCaml: assert false)")
  -- impl_mem.ml:978-983: Void, Array (_, None), Function, FunctionNoParams
  -- "must have a known size" → assert false (served-surface audit P3; was a
  -- silent MVunspecified)
  | _ => (.NoTaint, failwithI "CerbMem.reconstructValue: type without a known size (OCaml: assert false, impl_mem.ml:978-983)")

/-- Measured wrapper of the full reconstruction (fuel-free, hypothesis
    `CerbTagsWf.Acyclic ambient`; obligation `reconstructValueAbst_measure_sufficient`
    in CerbMem_lemMeasureProofs; register row `scripts/fuel_hypotheses.txt`). -/
def reconstructValueAbst [CerbGlobal.Switches] (enumDefs : EnumDefs) (ambient : TagDefs)
    (findOverlapping : Address → OverlapResult)
    (unionmap : List (Int × identifier))
    (funptrmap : Funptrmap) (addr : Int)
    (ty : ctype) (bytes : List AbsByte) : ProvTaint × MemValue :=
  reconstructValueAbst_lemFuel (CerbTagsWf.envBound ambient ty) enumDefs ambient findOverlapping unionmap funptrmap addr ty bytes

/-- The closure the default-pinned wrappers pass for `find_overlaping`: no
    allocation. At `⟨CerbGlobal.defaultSwitches⟩` the closure is never consulted
    (the pointer arm reads it only under `is_PNVI ()`), so its value is
    irrelevant there; it is NOT a model of `find_overlaping`. -/
def noOverlapping : Address → OverlapResult := fun _ => .NoAlloc

/-! ### The default-mode compatibility wrappers (PNVI arc S2, design §B.7)

`reconstructValue_lemFuel` / `reconstructValue` keep their pre-S2 names and
types for the consumer (cerberus-sl, statement §1.5 item 1 of the design
record): each is `reconstructValueAbst(_lemFuel)` pinned EXPLICITLY at
`⟨CerbGlobal.defaultSwitches⟩` (never the ambient instance — they are honestly
the DEFAULT-mode reconstruction), with the closure fixed to `noOverlapping` and
the taint discarded. Kernel-checked equal to the pre-S2 text:
`reconstructValue_lemFuel_eq_legacy` (test/Unit/ReconstructLegacyTest.lean,
compiled by row 1). NO production path calls these names (speedbump: rule W2 of
`scripts/check_no_fuel_numerals.sh`); `loadM` calls `reconstructValueAbst`. -/

/-- Default-mode reconstruction (compatibility wrapper; see above). -/
def reconstructValue_lemFuel (lemFuel : Nat) (enumDefs : EnumDefs) (ambient : TagDefs)
    (unionmap : List (Int × identifier))
    (funptrmap : Funptrmap) (addr : Int)
    (ty : ctype) (bytes : List AbsByte) : MemValue :=
  (@reconstructValueAbst_lemFuel ⟨CerbGlobal.defaultSwitches⟩ lemFuel enumDefs ambient noOverlapping unionmap funptrmap addr ty bytes).2

/-- Measured wrapper (C4): fuel-free, hypothesis `CerbTagsWf.Acyclic ambient`
    (its recursion is on the ctype being reconstructed, through member types
    read from the tag environment); obligation in CerbMem_lemMeasureProofs.
    Default-mode compatibility wrapper since PNVI arc S2 (text unchanged). -/
def reconstructValue (enumDefs : EnumDefs) (ambient : TagDefs) (unionmap : List (Int × identifier))
    (funptrmap : Funptrmap) (addr : Int)
    (ty : ctype) (bytes : List AbsByte) : MemValue :=
  reconstructValue_lemFuel (CerbTagsWf.envBound ambient ty) enumDefs ambient unionmap funptrmap addr ty bytes

/-! ## Memory-value typing — the store guard's helpers (audit-2 C3) -/

/-- typeof — impl_mem.ml:1115-1136. The ctype a mem_value inhabits;
    MVpointer's first component is the POINTEE type (impl_mem.ml:1123-1124).
    MVarray []: OCaml `assert false` ("ill-formed value",
    impl_mem.ml:1125-1127) — panic. Array element type from the FIRST
    element only (OCaml's own TODO shrug, impl_mem.ml:1128-1131). -/
def typeofMval_lemFuel (lemFuel : Nat) : MemValue → ctype :=
  fun mval =>
  match lemFuel with
  | 0 => fuelExhaustedWith "CerbMem.typeofMval: fuel exhausted" (mkCtype .Void0)
  | lemFuel + 1 =>
  match mval with
  | .MVunspecified (Ctype _ ty) => mkCtype ty
  | .MVinteger ity _ => mkCtype (.Basic (.Integer ity))
  | .MVfloating fty _ => mkCtype (.Basic (.Floating fty))
  | .MVpointer refTy _ => mkCtype (.Pointer no_qualifiers refTy)
  | .MVarray [] => failwithI "CerbMem.typeofMval: MVarray [] (OCaml: assert false, ill-formed value)"
  | .MVarray (mval :: rest) =>
    mkCtype (.Array0 (typeofMval_lemFuel lemFuel mval) (some ((rest.length + 1 : Nat) : Int)))
  | .MVstruct tagSym _ => mkCtype (.Struct tagSym)
  | .MVunion tagSym _ _ => mkCtype (.Union0 tagSym)

/-- MEASURED wrapper (C2): the counter starts from `memValueSize mval` (the
    recursion descends the MVarray head); fuel-free for every caller;
    `typeofMval_measure_sufficient` in CerbMem_lemMeasureProofs.lean. -/
def typeofMval (mval : MemValue) : ctype :=
  typeofMval_lemFuel (memValueSize mval) mval

/-- ctype_mem_compatible — impl_mem.ml:23-49: structural ctype equality
    after recursively erasing qualifiers, annotations and Atomic wrappers;
    Byte compares as unsigned char (impl_mem.ml:30-32); function-parameter
    is_register flags are dropped to false (impl_mem.ml:33-38, the
    `(_, ty, _) -> (..., false)` map). Used ONLY by the store guard. -/
def unqualifyAndUnatomic_lemFuel (lemFuel : Nat) : ctype → ctype_ :=
  fun cty =>
  match lemFuel with
  | 0 => fuelExhaustedWith "CerbMem.unqualifyAndUnatomic: fuel exhausted" .Void0
  | lemFuel + 1 =>
  match cty with
  | Ctype _ ty =>
    match ty with
    | .Void0 | .Basic _ | .Struct _ | .Union0 _ => ty
    | .Byte => .Basic (.Integer (.Unsigned .Ichar))
    | .Function (_, retTy) params variadic =>
      .Function (no_qualifiers, Ctype [] (unqualifyAndUnatomic_lemFuel lemFuel retTy))
        (params.map fun (p : qualifiers × ctype × Bool) =>
          (no_qualifiers, Ctype [] (unqualifyAndUnatomic_lemFuel lemFuel p.2.1), false))
        variadic
    | .FunctionNoParams (_, retTy) =>
      .FunctionNoParams (no_qualifiers, Ctype [] (unqualifyAndUnatomic_lemFuel lemFuel retTy))
    | .Array0 elemTy nOpt =>
      .Array0 (Ctype [] (unqualifyAndUnatomic_lemFuel lemFuel elemTy)) nOpt
    | .Pointer _ refTy =>
      .Pointer no_qualifiers (Ctype [] (unqualifyAndUnatomic_lemFuel lemFuel refTy))
    | .Atomic atomTy => unqualifyAndUnatomic_lemFuel lemFuel atomTy

/-- MEASURED wrapper (C2): structural on the ctype — the counter starts from
    the backend-derived `ctype.lemSize cty`; fuel-free for every caller;
    `unqualifyAndUnatomic_measure_sufficient` in CerbMem_lemMeasureProofs.lean
    (the worker and this wrapper are no longer `private` so the proof module can
    name them). -/
def unqualifyAndUnatomic (cty : ctype) : ctype_ :=
  unqualifyAndUnatomic_lemFuel (ctype.lemSize cty) cty

def ctypeMemCompatible (ty1 ty2 : ctype) : Bool :=
  ctypeEqual (Ctype [] (unqualifyAndUnatomic ty1)) (Ctype [] (unqualifyAndUnatomic ty2))

/-! ## Pointer value constructors — impl_mem.ml:1799-1827 -/

def nullPtrval (ty : ctype) : PointerValue :=
  .PV .Prov_none (.PVnull ty)

def funPtrval (s : sym) : PointerValue :=
  .PV .Prov_none (.PVfunction s)

def concretePtrval (allocId : Int) (addr : Int) : PointerValue :=
  .PV (.Prov_some allocId) (.PVconcrete none addr)

/-- case_ptrval — impl_mem.ml:1808-1814 -/
def casePtrval {α : Type} [Inhabited α] (pv : PointerValue)
    (onNull : ctype → α) (onFun : Option sym → α)
    (onConcrete : Option Int → Int → α) : α :=
  match pv with
  | .PV _ (.PVnull ty) => onNull ty
  | .PV _ (.PVfunction f) => onFun (some f)
  | .PV .Prov_none (.PVconcrete _ addr) => onConcrete none addr
  | .PV (.Prov_some i) (.PVconcrete _ addr) => onConcrete (some i) addr
  | .PV (.Prov_symbolic _) (.PVconcrete _ _) =>
    -- impl_mem.ml:1858 (THIS tree) `| _ -> failwith "case_ptrval"`, its
    -- `Prov_symbolic` HALF: an upstream crash on the PNVI path, REFUSED (design §G.1
    -- row R11, `R-PNVI-07`; PNVI arc S3). Unreachable at the default switch set
    -- (nothing mints `Prov_symbolic` there); the `Prov_device` half below is on the
    -- default path and is UNCHANGED (design §G.3, §H)
    failwithI (pnviRefusal "R-PNVI-07: case_ptrval, Prov_symbolic concrete pointer — impl_mem.ml:1858 `| _ -> failwith \"case_ptrval\"` (the Prov_symbolic half; the Prov_device half stays the mirrored fail-stop)")
  | .PV _ (.PVconcrete _ _) =>
    -- impl_mem.ml:1814 `| _ -> failwith "case_ptrval"` (a Prov_device or
    -- Prov_symbolic concrete pointer): an UNCAUGHT exception on the oracle
    -- (exit 125), mirrored as a fail-stop with the OCaml text (Q4). This
    -- used to be a fail-OPEN `onConcrete none addr` fallback — dead while no
    -- Prov_device pointer was ever minted, and a crash-to-VALUE conversion
    -- the moment Z-06 mirrored the device ranges (Z2-M-02, Z2 audit;
    -- tests/z2-probes/mem/device_funptr_call.c: calling through
    -- `(void(*)(void))0xABC` reaches this arm from core_eval.lem:920).
    failwithI "CerbMem.casePtrval: case_ptrval"

/-- case_funsym_opt — impl_mem.ml:1816-1827 -/
def caseFunsymOpt (st : MemState) (pv : PointerValue) : Option sym :=
  match pv with
  | .PV _ (.PVfunction s) => some s
  | .PV _ (.PVconcrete _ addr) =>
    match st.funptrmap.find? (fun (a, _) => a == addr) with
    | some (_, (fileDig, name)) => some (Symbol fileDig addr.toNat (SD_Id name))
    | none => none
  | _ => none

/-! ## Integer value constructors — impl_mem.ml:2361-2511 -/

def integerIval (n : Int) : IntegerValue := .IV .Prov_none n

/-- max_ival — impl_mem.ml:2367-2402. A reader CONSUMER (mem.lem): the
    generated call sites pass `enum_definitions` and `tagDefs` first. Enum is
    resolved FIRST through the program's enum map (impl_mem.ml:2369-2372
    resolves it through the DefaultImpl registry, ocaml_implementation.ml:
    124-150 — the same information, as data since program-data parameters
    E-A 2026-09-20; zero-discrepancy Z2-M-14's probe
    tests/z2-probes/mem/enum_conv.c AGREES on all three engines).
    Bool: OCaml uses unsigned_max = 255 (its own "TODO: not sure about
    this (maybe it should be 1 ...)" at impl_mem.ml:2385-2387 — mirrored
    as-is). Char: signed (DefaultImpl char_is_signed = true,
    ocaml_implementation.ml:257). Wchar_t: unsigned_max
    (impl_mem.ml:2388-2392); Wint_t: signed_max (impl_mem.ml:2393-2396).
    Missing sizeof: OCaml failwith → panic. -/
def maxIval (enumDefs : EnumDefs) (_tagDefs : TagDefs) (ity : integerType) : IntegerValue :=
  let ity := CerberusImpl.resolveEnum enumDefs ity   -- impl_mem.ml:2369-2372, through the map
  let size := match CerberusImpl.sizeof_ity ity with
    | some n => n
    | none => failwithI "CerbMem.maxIval: the concrete memory model requires a complete implementation MAX"
  let signedMax : Int := (2 ^ (size * 8 - 1)) - 1
  let unsignedMax : Int := (2 ^ (size * 8)) - 1
  integerIval (match ity with
    | .Char0 => if CerberusImpl.is_signed_ity .Char0 then signedMax else unsignedMax
    | .Bool0 => unsignedMax          -- 255, OCaml's own TODO behavior
    | .Size_t | .Wchar_t | .Unsigned _ => unsignedMax
    | .Ptrdiff_t | .Wint_t | .Signed _ => signedMax
    | .Ptraddr_t => unsignedMax
    | .Enum0 _ => failwithI "maxIval: Enum after resolveEnum (OCaml: assert false)")

/-- min_ival — impl_mem.ml:2405-2434. A reader consumer like max_ival; Enum
    resolved through the map (impl_mem.ml:2407-2410 through the registry). Char: signed → -2^7 (OCaml hardcodes 8-1
    bits, impl_mem.ml:2412-2416). Bool/Size_t/Wchar_t/Wint_t/Unsigned:
    zero (impl_mem.ml:2417-2424 — note Wint_t is UNSIGNED here but
    SIGNED in max_ival; OCaml's asymmetry, mirrored). Ptrdiff_t/Signed:
    -2^(8n-1) (impl_mem.ml:2425-2432). -/
def minIval (enumDefs : EnumDefs) (_tagDefs : TagDefs) (ity : integerType) : IntegerValue :=
  let ity := CerberusImpl.resolveEnum enumDefs ity   -- impl_mem.ml:2407-2410, through the map
  integerIval (match ity with
    | .Char0 =>
      if CerberusImpl.is_signed_ity .Char0 then -(2 ^ (8 - 1)) else 0
    | .Bool0 | .Size_t | .Wchar_t | .Wint_t | .Unsigned _ => 0
    | .Ptrdiff_t | .Signed _ =>
      match CerberusImpl.sizeof_ity ity with
      | some n => -(2 ^ (n * 8 - 1))
      | none => failwithI "CerbMem.minIval: the concrete memory model requires a complete implementation MIN"
    | .Ptraddr_t => 0
    | .Enum0 _ => failwithI "minIval: Enum after resolveEnum (OCaml: assert false)")

def sizeofIval [LemFuel] (enumDefs : EnumDefs) (tagDefs : TagDefs) (ty : ctype) : IntegerValue := integerIval (sizeofCtype enumDefs tagDefs ty)
def alignofIval [LemFuel] (enumDefs : EnumDefs) (tagDefs : TagDefs) (ty : ctype) : IntegerValue := integerIval (alignofCtype enumDefs tagDefs ty)

/-- concurRead_ival — impl_mem.ml:2361-2362 `failwith "TODO: concurRead_ival"`,
    mirrored as a fail-stop with the OCaml text (zero-discrepancy Z2-M-07:
    this returned `integerIval 0`, a dead fail-OPEN path). Reachability:
    only through the concurrency mode, which is REFUSED (Z-24/Z-25) and
    non-functional on the oracle itself. -/
def concurReadIval (_ : integerType) (_ : sym) : IntegerValue :=
  failwithI "CerbMem.concurReadIval: TODO: concurRead_ival"

/-! ### Integer division/remainder helpers

    OCaml's `Z` in impl_mem.ml (impl_mem.ml:7-13) extends zarith with
      let integerRem_t = (mod)                  — zarith `Z.(mod)` = `Z.rem`
      let integerRem_f = Big_int_Z.mod_big_int  — zarith's legacy-Big_int mod
    Verified against zarith (z.mli:160-168, 820-821, and empirically):
      Z.div        : TRUNCATING quotient (round toward zero): -7/2 = -3
      Z.rem        : truncating remainder, sign of the DIVIDEND:
                     rem 7 (-2) = 1, rem (-7) 2 = -1
      mod_big_int  : EUCLIDEAN remainder, always non-negative (NOT
                     flooring): mod_big_int (-7) 2 = 1,
                     mod_big_int (-7) (-2) = 1 (floor would give -1)
    Lean's Int `/`/`%` are ediv/emod — NOT these; use the explicit forms.
    Zero divisor (zero-discrepancy Z2-M-01): zarith raises
    `Division_by_zero` (z.mli:158-168; the Big_int_Z mod likewise) and
    impl_mem.ml has NO guard on IntRem_t/IntRem_f (upstream
    deps/cerberus-upstream/memory/concrete/impl_mem.ml:2481-2484; fork
    :2525-2528) — an UNCAUGHT exception on the oracle (exit 125), REACHABLE
    FROM C through `runtime/libcore/std.core:385` (aligned_alloc_proxy's
    `size rem_t align`: `aligned_alloc(0, n)` crashes fork AND upstream).
    MIRRORED as a loud fail-stop (`failwithI`, the mechanism `opIval`'s
    IntExp arm uses), 2026-10-03 under [USER 2026-10-03] "we don't innovate
    wrt Cerberus-upstream, unless something is very very very obviously a
    bug ... we should fall back to loudly rejecting (either as unsupported,
    or matching upstream)". This supersedes the 2026-09-04 interim (total
    `Int.tmod`/`emod`, x mod 0 = x, which answered `aligned_alloc(0, 8)` with
    a `DUMMY(align_alloc)` UB upstream never chooses) and withdraws the Z2
    record §10.1 recommendation (addendum there; record
    docs/2026-10-03_total-arith-and-bookkeeping-record.md). Witnesses:
    tests/immaculate/{libc,nolibc}/zd-z2m01-* — both-crash `MATCH | L=CRASH`.
    IntDiv has the oracle's own explicit zero guard (:2479-2480, mirrored in
    `opIval`); diff_ptrval's `Z.div` (:1967) divides by sizeof(elem) and
    raises on 0 like the helper below. -/

/-- Z.div — truncating quotient (zarith z.mli:155-162). zarith raises
    `Division_by_zero` on a zero divisor: mirrored as a fail-stop. -/
def integerDiv_t (a b : Int) : Int :=
  if b == 0 then failwithI "CerbMem.integerDiv_t: Division_by_zero (zarith Z.div raises; mirrors the oracle's uncaught exception, impl_mem.ml:1967 diff_ptrval)"
  else Int.tdiv a b
/-- Z.integerRem_t = Z.rem — truncating remainder, sign of dividend
    (impl_mem.ml:11, zarith z.mli:164-168). zarith raises
    `Division_by_zero` on a zero divisor: mirrored as a fail-stop. -/
def integerRem_t (a b : Int) : Int :=
  if b == 0 then failwithI "CerbMem.integerRem_t: Division_by_zero (zarith Z.rem raises; mirrors the oracle's uncaught exception, impl_mem.ml:2481-2482 op_ival IntRem_t)"
  else Int.tmod a b
/-- Z.integerRem_f = Big_int_Z.mod_big_int — euclidean remainder,
    always non-negative (impl_mem.ml:12). Lean's Int.emod is exactly
    euclidean remainder. `mod_big_int` raises `Division_by_zero` on a zero
    divisor: mirrored as a fail-stop. -/
def integerRem_f (a b : Int) : Int :=
  if b == 0 then failwithI "CerbMem.integerRem_f: Division_by_zero (Big_int_Z.mod_big_int raises; mirrors the oracle's uncaught exception, impl_mem.ml:2483-2484 op_ival IntRem_f)"
  else Int.emod a b

/-- op_ival — impl_mem.ml:2464-2490 -/
def opIval (op : integer_operator) (v1 v2 : IntegerValue) : IntegerValue :=
  match v1, v2 with
  | .IV prov1 n1, .IV prov2 n2 =>
    match op with
    | .IntAdd => .IV (combineProv prov1 prov2) (n1 + n2)
    | .IntSub =>
      -- provenance special case — impl_mem.ml:2469-2475: Sub forwards
      -- prov1 only when prov1 is Prov_some/device and prov2 is not
      -- Prov_some (ptr − int keeps the pointer's provenance; ptr − ptr
      -- and int − anything lose it)
      let prov' := match prov1, prov2 with
        | .Prov_some _, .Prov_some _ => Provenance.Prov_none
        | .Prov_none, _ => Provenance.Prov_none
        | _, _ => prov1
      .IV prov' (n1 - n2)
    | .IntMul => .IV (combineProv prov1 prov2) (n1 * n2)
    | .IntDiv =>
      -- impl_mem.ml:2479-2480: explicit zero guard, then TRUNCATING Z.div
      .IV (combineProv prov1 prov2) (if n2 == 0 then 0 else integerDiv_t n1 n2)
    -- impl_mem.ml:2481-2484 (upstream; fork :2525-2528): NO zero guard —
    -- the helpers fail-stop on 0 as zarith raises (Z2-M-01, note above)
    | .IntRem_t => .IV (combineProv prov1 prov2) (integerRem_t n1 n2)
    | .IntRem_f => .IV (combineProv prov1 prov2) (integerRem_f n1 n2)
    | .IntExp =>
      -- impl_mem.ml:2485-2490: Prov_none (shift elaboration forwards the
      -- LEFT operand's provenance elsewhere); `Z.pow n1 (Z.to_int n2)`. A
      -- NEGATIVE exponent raises `Invalid_argument` in zarith (z.mli:636).
      -- The model gives `^` no meaning at a negative exponent, so under the
      -- [USER 2026-10-03] synthesis ("(1) agree with this": no answer
      -- defined → a loud stop mirroring the crash) this is a fail-stop, not
      -- the fail-OPEN `.toNat` clamp that stood here. Unreachable from C: the
      -- shift elaboration guards negative counts (UB) before the `^` (std.core
      -- shift procs).
      if n2 < 0 then failwithI "CerbMem.opIval IntExp: negative exponent has no meaning in the model (impl_mem.ml:2490 Z.pow raises Invalid_argument — mirrored as a fail-stop); unreachable behind the shift guards"
      else .IV Provenance.Prov_none (n1 ^ n2.toNat)

/-- offsetof_ival — impl_mem.ml:2193-2201: offsetsof (WITHOUT
    ignore_flexible — OCaml uses the default there), member found by NAME
    (ident_equal = idEqual); union members are all at offset 0 via
    offsetsof's union arm. Missing member: OCaml failwith — panic here
    (the previous code silently returned 0 and compared identifiers
    location-sensitively with BEq). -/
def offsetofIval [LemFuel] (enumDefs : EnumDefs) (tagDefs : TagDefs) (tagDefsMap : CerbTags.TagDefsMap) (tag : sym) (memb : identifier) : IntegerValue :=
  -- target_rep for lem offsetof_ival (mem.lem:257): the lem-side argument
  -- is the tag map, threaded through the whole layout family (2026-09-01
  -- S-basket item 1 — the elaboration-time fold's only tag source).
  -- It is also the ambient map: sizeof/alignof read union tags from the
  -- ambient (impl_mem.ml's Tags.tagDefs ()), which is still empty while
  -- AilEoffsetof is folded during elaboration, so offsetof in a struct with a
  -- union member panicked. At run time both maps are the global, so this
  -- changes nothing after elaboration.
  let (xs, _) := offsetsof enumDefs tagDefsMap tagDefsMap tag
  match xs.find? (fun (ident, _, _) => idEqual ident memb) with
  | some (_, _, off) => integerIval off
  | none => failwithI "Concrete.offsetof_ival: invalid memb_ident"

/-! ## Bitwise operations — impl_mem.ml:2497-2511: pure two's-complement
    arithmetic on unbounded Z — `Z.(sub (neg n) (of_int 1))`, `Z.logand`,
    `Z.logor`, `Z.logxor` — and the integerType argument is IGNORED
    (`_`). Lean's `Int.not`/`Int.land`/`Int.lor`/`Int.xor` are the same
    infinite two's-complement operations. Zero-discrepancy Z2-M-08 (audit
    §2.1.1 / literal census #3): this used to re-normalise the operands
    through a `sizeof_ity` width with a fail-OPEN `| none => 4` default
    the OCaml never reads; value-equal for in-range operands, deleted. -/

/-- Infinite two's-complement bitwise ops on Int (zarith `Z.logand`/`Z.logor`/
    `Z.logxor` = GMP `mpz_and/ior/xor` semantics), which Lean 4.32 core does
    not provide for `Int` (only `Int.not`/shifts). Written on Nat via the
    standard identities with `~n = -n-1`: for a, b ≥ 0 the Nat ops; with
    a' = ~a ≥ 0 for a negative operand, `a & b = b - (b & a')`,
    `a | b = ~(a' - (a' & b))`, `a ^ b = ~(a' ^ b)`; both negative:
    `a & b = ~(a' | b')`, `a | b = ~(a' & b')`, `a ^ b = a' ^ b'`.
    Checked below on signed examples by `decide`. -/
private def zNot (a : Int) : Int := -a - 1
def zLogand (a b : Int) : Int :=
  match a, b with
  | .ofNat m, .ofNat n => .ofNat (m &&& n)
  | .ofNat m, .negSucc n => .ofNat (m - (m &&& n))
  | .negSucc m, .ofNat n => .ofNat (n - (n &&& m))
  | .negSucc m, .negSucc n => zNot (.ofNat (m ||| n))
def zLogor (a b : Int) : Int :=
  match a, b with
  | .ofNat m, .ofNat n => .ofNat (m ||| n)
  | .ofNat m, .negSucc n => zNot (.ofNat (n - (n &&& m)))
  | .negSucc m, .ofNat n => zNot (.ofNat (m - (m &&& n)))
  | .negSucc m, .negSucc n => zNot (.ofNat (m &&& n))
def zLogxor (a b : Int) : Int :=
  match a, b with
  | .ofNat m, .ofNat n => .ofNat (m ^^^ n)
  | .ofNat m, .negSucc n => zNot (.ofNat (m ^^^ n))
  | .negSucc m, .ofNat n => zNot (.ofNat (m ^^^ n))
  | .negSucc m, .negSucc n => .ofNat (m ^^^ n)
-- reference values: GMP two's complement (-6 = …11111010, 3 = …00000011, -3 = …11111101)
example : zLogand (-6) 3 = 2 := by decide
example : zLogand (-6) (-3) = -8 := by decide
example : zLogand 5 (-1) = 5 := by decide
example : zLogor (-6) 3 = -5 := by decide
example : zLogor (-6) (-3) = -1 := by decide
example : zLogor 5 (-8) = -3 := by decide
example : zLogxor (-6) 3 = -7 := by decide
example : zLogxor (-6) (-3) = 7 := by decide
example : zLogxor 5 (-1) = -6 := by decide

def bitwiseComplementIval (_ : integerType) (v : IntegerValue) : IntegerValue :=
  match v with
  | .IV prov n => .IV prov (-n - 1)                               -- :2500

def bitwiseAndIval (_ : integerType) (v1 v2 : IntegerValue) : IntegerValue :=
  match v1, v2 with
  | .IV prov1 n1, .IV prov2 n2 => .IV (combineProv prov1 prov2) (zLogand n1 n2)   -- :2504

def bitwiseOrIval (_ : integerType) (v1 v2 : IntegerValue) : IntegerValue :=
  match v1, v2 with
  | .IV prov1 n1, .IV prov2 n2 => .IV (combineProv prov1 prov2) (zLogor n1 n2)    -- :2507

def bitwiseXorIval (_ : integerType) (v1 v2 : IntegerValue) : IntegerValue :=
  match v1, v2 with
  | .IV prov1 n1, .IV prov2 n2 => .IV (combineProv prov1 prov2) (zLogxor n1 n2)   -- :2510

/-! ## Integer value destructors — impl_mem.ml:2513-2562 -/

/-- case_integer_value — impl_mem.ml:2513-2514
    In the concrete model, always calls f_concrete -/
def caseIntegerValue {α : Type} (iv : IntegerValue)
    (onSpecified : Int → α) (_ : Unit → α) : α :=
  match iv with | .IV _ n => onSpecified n

def isSpecifiedIval (_ : IntegerValue) : Bool := true

def eqIval (v1 v2 : IntegerValue) : Option Bool :=
  match v1, v2 with | .IV _ n1, .IV _ n2 => some (n1 == n2)
def ltIval (v1 v2 : IntegerValue) : Option Bool :=
  match v1, v2 with | .IV _ n1, .IV _ n2 => some (n1 < n2)
def leIval (v1 v2 : IntegerValue) : Option Bool :=
  match v1, v2 with | .IV _ n1, .IV _ n2 => some (n1 ≤ n2)

/-! TRIPWIRE (zero-discrepancy Z-59 / Z2-M-19, charter §2.7): the three
    comparisons above are TOTAL `some`, mirroring impl_mem.ml:2600-2606
    (`Some (Z.equal …)` / `Some (Z.compare … = -1)` / `Some (cmp = -1 ||
    cmp = 0)`). This is the premise of CerbND's no-`NDguard` argument
    (CerbND.lean header): `PEconstrained` arises only from a `Nothing`
    here (core_eval.lem:352-378), so `addConstraints` (driver.lem:148)
    never runs and the oracle's `with_constraints`/`check_sat`
    (smt2.ml:42-44) is never reached. If any of these ever returns
    `none`, these theorems fail to build and the SMT path must be ported. -/
theorem eqIval_isSome (v1 v2 : IntegerValue) : (eqIval v1 v2).isSome = true := by
  cases v1; cases v2; rfl
theorem ltIval_isSome (v1 v2 : IntegerValue) : (ltIval v1 v2).isSome = true := by
  cases v1; cases v2; rfl
theorem leIval_isSome (v1 v2 : IntegerValue) : (leIval v1 v2).isSome = true := by
  cases v1; cases v2; rfl

/-! ## Floating value operations — impl_mem.ml:2519-2554 -/

def zeroFval : FloatingValue := 0.0
def oneFval : FloatingValue := 1.0
def strFval (s : String) : FloatingValue := CerbFloat.of_string s

/-- case_fval — impl_mem.ml:2526-2527
    In the concrete model, always calls fconcrete -/
def caseFval {α : Type} (fv : FloatingValue) (_ : Unit → α) (onConcrete : Float → α) : α :=
  onConcrete fv

def opFval (op : floating_operator) (v1 v2 : FloatingValue) : FloatingValue :=
  match op with
  | .FloatAdd => v1 + v2 | .FloatSub => v1 - v2
  | .FloatMul => v1 * v2 | .FloatDiv => v1 / v2

def eqFval (v1 v2 : FloatingValue) : Bool := v1 == v2
def ltFval (v1 v2 : FloatingValue) : Bool := v1 < v2
def leFval (v1 v2 : FloatingValue) : Bool := v1 <= v2

def fvfromint (iv : IntegerValue) : FloatingValue :=
  match iv with | .IV _ n => Float.ofInt n
/-- ivfromfloat — impl_mem.ml:2553-2554: `IV (Prov_none, Z.of_float fval)`.
    Z.of_float truncates toward ZERO keeping the sign (verified against
    zarith: of_float (-2.9) = -2); CerbFloat.truncToInt mirrors that
    bit-exactly (the previous Float.toUInt64 path clamped all negatives
    to 0 — survey finding 6). NaN/inf: Z.of_float raises Z.Overflow,
    mirrored by truncToInt's panic. -/
def ivfromfloat (_ : integerType) (fv : FloatingValue) : IntegerValue :=
  integerIval (CerbFloat.truncToInt fv)

/-! ## Memory value constructors — impl_mem.ml:2564-2595 -/

def unspecifiedMval (ty : ctype) : MemValue := .MVunspecified ty
def integerValueMval (ity : integerType) (iv : IntegerValue) : MemValue := .MVinteger ity iv
def floatingValueMval (fty : floatingType) (fv : FloatingValue) : MemValue := .MVfloating fty fv
def pointerMval (ty : ctype) (pv : PointerValue) : MemValue := .MVpointer ty pv
def arrayMval (elems : List MemValue) : MemValue := .MVarray elems
def structMval (tag : sym) (members : List (identifier × ctype × MemValue)) : MemValue := .MVstruct tag members
def unionMval (tag : sym) (member : identifier) (value : MemValue) : MemValue := .MVunion tag member value

/-- case_mem_value — impl_mem.ml:2579-2594
    The f_concur callback is never called in the concrete model -/
def caseMemValue {α : Type} (mv : MemValue)
    (onUnspec : ctype → α) (onConcurRead : integerType → sym → α)
    (onInt : integerType → IntegerValue → α) (onFloat : floatingType → FloatingValue → α)
    (onPtr : ctype → PointerValue → α) (onArray : List MemValue → α)
    (onStruct : sym → List (identifier × ctype × MemValue) → α)
    (onUnion : sym → identifier → MemValue → α) : α :=
  match mv with
  | .MVunspecified ty => onUnspec ty
  | .MVinteger ity iv => onInt ity iv
  | .MVfloating fty fv => onFloat fty fv
  | .MVpointer ty pv => onPtr ty pv
  | .MVarray elems => onArray elems
  | .MVstruct tag members => onStruct tag members
  | .MVunion tag member val_ => onUnion tag member val_

/-! ## Pure pointer operations — impl_mem.ml -/

/-- array_shift_ptrval (the PURE shift) — impl_mem.ml:2203-2221, arm for
    arm: `sz = if is_void ty then 1 else sizeof ty` (:2206, the GNU
    byte-granular extension), `offset = sz * ival` (:2207); a Prov_symbolic
    provenance → upstream's failwith (:2209-2211), REFUSED since PNVI arc S3
    (`R-PNVI-06`, the arm's comment); null → failwith (:2214-2217);
    PVfunction → failwith (:2218-2219); concrete → the shifted address with
    the union-member tag KEPT (:2220-2221). The failwiths are fail-stops
    with the OCaml texts (Q4). -/
def arrayShiftPtrval [LemFuel] (enumDefs : EnumDefs) (tagDefs : TagDefs) (pv : PointerValue) (elemTy : ctype) (iv : IntegerValue) : PointerValue :=
  match pv, iv with
  | .PV prov base, .IV _ ival =>
    let sz : Int := match elemTy with
      | Ctype _ .Void0 => 1
      | _ => Int.ofNat (sizeofCtype enumDefs tagDefs elemTy)
    let offset := sz * ival
    match prov, base with
    | .Prov_symbolic _, _ =>
      -- impl_mem.ml:2254-2255 (THIS tree) `failwith "Concrete.array_shift_ptrval
      -- found a Prov_symbolic"` — an upstream crash on the PNVI path, REFUSED (design
      -- §G.1 row R8, class (A), `R-PNVI-06`; PNVI arc S3). The function is on the
      -- default path; THIS arm is not (nothing mints `Prov_symbolic` at the default
      -- switch set)
      failwithI (pnviRefusal "R-PNVI-06: array_shift_ptrval (pure), Prov_symbolic pointer — impl_mem.ml:2254-2255 `failwith \"Concrete.array_shift_ptrval found a Prov_symbolic\"`")
    | _, .PVnull _ =>
      failwithI s!"CerbMem.arrayShiftPtrval: TODO(pure shift a null pointer should be undefined behaviour), offset:{offset}"
    | _, .PVfunction _ => failwithI "Concrete.array_shift_ptrval, PVfunction"
    | _, .PVconcrete um addr => .PV prov (.PVconcrete um (addr + offset))

/-- member_shift_ptrval — impl_mem.ml:2223-2242.
    Shift pointer to struct/union member. Uses CerbTags.tagDefs () to look up
    the struct layout. For unions, all members are at offset 0 but we record
    which member we're pointing to (in PVconcrete's unionMember field). -/
def memberShiftPtrval [LemFuel] (enumDefs : EnumDefs) (tagDefs : TagDefs) (pv : PointerValue) (tag : sym) (memb : identifier) : PointerValue :=
  let tagDefsAsList : List (sym × (CerbLocation.Loc × tag_definition)) :=
    fmapElements tagDefs
  let (.IV _ offsetVal) := offsetofIval enumDefs tagDefs tagDefs tag memb
  let isUnion := match tagDefsAsList.find? (fun (s, _) => symbolEquality s tag) with
    | some (_, (_, UnionDef _)) => true
    | _ => false
  let unionMem := if isUnion then some memb else none
  match pv with
  | .PV prov (.PVnull ty) =>
    if offsetVal == 0 then .PV prov (.PVnull ty)
    else .PV prov (.PVconcrete unionMem offsetVal)
  | .PV _ (.PVfunction _) =>
    -- impl_mem.ml:2239-2240: failwith "Concrete.member_shift_ptrval,
    -- PVfunction" — mirrored as a panic (arc-14 S1 F1, sem:S8; was a
    -- self-confessed fail→value divergence returning pv unchanged).
    failwithI "Concrete.member_shift_ptrval, PVfunction (impl_mem.ml:2239-2240)"
  | .PV prov (.PVconcrete _ addr) =>
    .PV prov (.PVconcrete unionMem (addr + offsetVal))

/-- bytefromint — impl_mem.ml:2775-2777: `assert (0 ≤ n ≤ 255)`, value
    returned UNCHANGED (no wrap). The assert is mirrored as a panic
    (arc-14 S1 F1, sem:S6; was: silent euclidean `n % 256` wrap — a
    crash-path turned value-path). -/
def bytefromint (iv : IntegerValue) : IntegerValue :=
  match iv with
  | .IV _ n =>
    if 0 ≤ n && n ≤ 255 then iv
    else failwithI "CerbMem.bytefromint: value out of byte range (impl_mem.ml:2776 assert)"

/-- intfrombyte — impl_mem.ml:2779-2781: same assert, value unchanged
    (arc-14 S1 F1, sem:S6; the assert was previously dropped). -/
def intfrombyte (iv : IntegerValue) : IntegerValue :=
  match iv with
  | .IV _ n =>
    if 0 ≤ n && n ≤ 255 then iv
    else failwithI "CerbMem.intfrombyte: value out of byte range (impl_mem.ml:2780 assert)"

/-- overlapping — impl_mem.ml:527-532 -/
def overlapping (f1 f2 : Footprint) : Bool :=
  match f1, f2 with
  | .FP .R _ _, .FP .R _ _ => false  -- two reads never overlap
  | .FP _ b1 sz1, .FP _ b2 sz2 =>
    !(b1 + sz1 ≤ b2 || b2 + sz2 ≤ b1)

/-- The initial memory state at address-space top `addressSpaceTop` — impl_mem.ml:503-516
    `initial_mem_state`, whose `last_address` was the literal `0xFFFFFFFFFFFF` (:508, "a random
    impl-def choice") until the address-space-bound slice (2026-09-17; [USER 2026-09-16] "the
    semantics should be quantified over such bounds"): the top is a PARAMETER threaded from
    the driver's entry (`initial_driver_state`, and the desugar state for the const-expr
    mini-run), so a consumer theorem quantifies `∀ top`; matched mode instantiates upstream's
    value from `Main.lean` `defaultAddressSpaceTop` (`--address-space-top N`). Every other
    field is the OCaml record's empty/zero. -/
def initialMemState (addressSpaceTop : Int) : MemState := { lastAddress := addressSpaceTop }

/-! ## Pretty-printing (arc-10 S3 — real mirrors of the OCaml printers)

The OCaml concrete model's pp section lives at impl_mem.ml:560-615 and
reaches into the shared printers Pp_symbol (pp_symbol.ml) and
Pp_core_ctype (pp_core_ctype.ml). PLACEMENT NOTE: the Lean import graph
forces the shared symbol/ctype mirrors to live HERE rather than in
CerbPP.lean — CerbPP imports Core, which imports Mem → CerbMem, so
CerbMem is the lowest hand-written module that sees ctype/sym and is
seen by everything that pretty-prints. CerbPP delegates to these.
All output is colour-free: every mirrored OCaml path is wrapped in
Cerb_colour.without_colour (e.g. driver_ocaml.ml:79) or prints through
plain-text `!^`. -/

/-- Mirrors Pp_symbol.to_string (pp_symbol.ml:5-10). -/
def ppSymbolRaw : sym → String
  | .Symbol _ n sd =>
    match sd with
    | .SD_Id str | .SD_ObjectAddress str | .SD_FunArgValue str =>
      str ++ "_" ++ toString n
    | _ => "a_" ++ toString n

/-- Mirrors Pp_symbol.to_string_pretty (pp_symbol.ml:12-35) with
    is_human = false (the default; every caller mirrored here uses it). -/
def ppSymbol : sym → String
  | .Symbol _ n sd =>
    -- pp_symbol.ml:13-19: name{n} at debug_level > 4, else the bare name
    let maybeAddNumber (name : String) : String :=
      if CerbDebug.get_level () > 4 then name ++ "{" ++ toString n ++ "}"
      else name
    match sd with
    | .SD_Id str | .SD_ObjectAddress str | .SD_FunArgValue str =>
      maybeAddNumber str
    | .SD_unnamed_tag _ => "__cerbty_unnamed_tag_" ++ toString n  -- is_human=false arm (pp_symbol.ml:25-29)
    | .SD_CN_Id str => str
    | _ => "a_" ++ toString n  -- SD_None / SD_Return / SD_FunArg (pp_symbol.ml:33-34)

/-- Mirrors Pp_symbol.pp_identifier (pp_symbol.ml:99-103), clever=false.
    DELIBERATE DIVERGENCE (documented): at debug_level ≥ 5 OCaml prepends
    the pp'd location; we never do (debug-only path, location pp is the
    registered pretty-printer-arc residual). -/
def ppIdentifier : identifier → String
  | .Identifier _ str => str

/-- Mirrors Pp_core_ctype.pp_integer_base_ctype (pp_core_ctype.ml:18-30). -/
def ppIntegerBaseCtype : integerBaseType → String
  | .Ichar => "ichar"
  | .Short => "short"
  | .Int_ => "int"
  | .Long => "long"
  | .LongLong => "long_long"
  | .IntN_t n => "int" ++ toString n ++ "_t"
  | .Int_leastN_t n => "int_least" ++ toString n ++ "_t"
  | .Int_fastN_t n => "int_fast" ++ toString n ++ "_t"
  | .Intmax_t => "intmax_t"
  | .Intptr_t => "intptr_t"

/-- The fixed-width class special-cased at pp_core_ctype.ml:36-39. -/
private def isStdlibIbty : integerBaseType → Bool
  | .IntN_t _ | .Int_leastN_t _ | .Int_fastN_t _ | .Intmax_t | .Intptr_t => true
  | _ => false

/-- Mirrors Pp_core_ctype.pp_integer_ctype (pp_core_ctype.ml:33-47);
    the ?compact flag is unused in the OCaml body and omitted here. -/
def ppIntegerCtype : integerType → String
  | .Char0 => "char"
  | .Bool0 => "_Bool"
  | .Signed ibty =>
    if isStdlibIbty ibty then ppIntegerBaseCtype ibty
    else "signed " ++ ppIntegerBaseCtype ibty
  | .Unsigned ibty =>
    if isStdlibIbty ibty then "u" ++ ppIntegerBaseCtype ibty
    else "unsigned " ++ ppIntegerBaseCtype ibty
  | .Enum0 s => "enum " ++ ppSymbol s
  | .Size_t => "size_t"
  | .Wchar_t => "wchar_t"
  | .Wint_t => "wint_t"
  | .Ptrdiff_t => "ptrdiff_t"
  | .Ptraddr_t => "ptraddr_t"

/-- Mirrors Pp_core_ctype.pp_floating_ctype (pp_core_ctype.ml:50-57). -/
def ppFloatingCtype : floatingType → String
  | .RealFloating .Float0 => "float"
  | .RealFloating .Double => "double"
  | .RealFloating .LongDouble => "long_double"

/-- Mirrors Pp_core_ctype.pp_basic_ctype (pp_core_ctype.ml:60-63). -/
def ppBasicCtype : basicType → String
  | .Integer ity => ppIntegerCtype ity
  | .Floating fty => ppFloatingCtype fty

mutual
/-- Mirrors Pp_core_ctype.pp_ctype (pp_core_ctype.ml:66-90). Array sizes
    print via Pp_ail.pp_integer = Z.to_string (pp_ail.ml:103). The
    OCaml TODOs that drop qualifiers (Function/Pointer arms) are
    mirrored as-is: qualifiers are never printed. -/
def ppCtype : ctype → String
  | .Ctype _ ty => ppCtype_ ty

def ppCtype_ : ctype_ → String
  | .Void0 => "void"
  | .Basic bty => ppBasicCtype bty
  | .Array0 elemTy nOpt =>
    ppCtype elemTy ++ "[" ++ (match nOpt with | some n => toString n | none => "") ++ "]"
  | .Function (_, retTy) argTys isVariadic =>
    ppCtype retTy ++ " (" ++ ppCtypeParams argTys
      ++ (if isVariadic then ", ..." else "") ++ ")"
  | .FunctionNoParams (_, retTy) => ppCtype retTy ++ " ()"
  | .Pointer _ refTy => ppCtype refTy ++ "*"
  | .Atomic atomTy => "_Atomic (" ++ ppCtype atomTy ++ ")"
  | .Struct s => "struct " ++ ppSymbol s
  | .Union0 s => "union " ++ ppSymbol s
  | .Byte => "byte"

/-- comma_list over the parameter triples (pp_core_ctype.ml:76-78). -/
def ppCtypeParams : List (qualifiers × ctype × Bool) → String
  | [] => ""
  | [(_, ty, _)] => ppCtype ty
  | (_, ty, _) :: rest => ppCtype ty ++ ", " ++ ppCtypeParams rest
end

/-- Mirrors string_of_provenance (impl_mem.ml:550-558). -/
def stringOfProvenance : Provenance → String
  | .Prov_none => "@empty"
  | .Prov_some allocId => "@" ++ toString allocId
  | .Prov_symbolic iota => "@iota(" ++ toString iota ++ ")"
  | .Prov_device => "@device"

/-- Mirrors `"0x" ^ Z.format "%x" n` (impl_mem.ml:572). Addresses are
    nonnegative in the concrete model; a negative Int would print as its
    toNat clamp (0) — unreachable, kept total. -/
private def hexOfAddress (n : Int) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 n.toNat)

/-- Mirrors pp_ctype used with `stringFromCtype` — mem.lem:411-413's
    declared OCaml referent (`String_Ctype.string_of_ctype`) does not
    exist upstream (dead val on the OCaml side); we point it at the same
    Pp_core_ctype text as every other ctype pp. -/
def stringFromCtype (ty : ctype) : String := ppCtype ty

/-- Mirrors pp_integer_value (impl_mem.ml:576-580);
    Impl_mem.string_of_integer_value (impl_mem.ml:3004-3005) and
    pp_integer_value_for_core (impl_mem.ml:582) both resolve to it. -/
def stringFromIntegerValue : IntegerValue → String
  | .IV prov n =>
    if CerbDebug.get_level () ≥ 3 then
      "<" ++ stringOfProvenance prov ++ ">:" ++ toString n
    else
      toString n

/-- Mirrors pp_pointer_value (impl_mem.ml:598-608); the ?is_verbose flag
    is unused in the OCaml body. -/
def stringFromPointerValue : PointerValue → String
  | .PV prov base =>
    match base with
    | .PVnull ty => "NULL(" ++ ppCtype ty ++ ")"
    | .PVfunction s => "Cfunction(" ++ ppSymbol s ++ ")"
    | .PVconcrete _ n =>
      "(" ++ stringOfProvenance prov ++ ", " ++ hexOfAddress n ++ ")"

mutual
/-- Mirrors pp_mem_value (impl_mem.ml:591-615), exactly — incl. the
    quirky `equals ^^^` spacing (".m= v") and `braces(comma_list …)`
    for arrays. Total (was `partial`; arc-10 S3). -/
def stringFromMemValue : MemValue → String
  | .MVunspecified _ => "UNSPEC"
  | .MVinteger _ ival => stringFromIntegerValue ival
  | .MVfloating _ fval => CerbFloat.string_of_float fval
  | .MVpointer _ ptrval => "ptr(" ++ stringFromPointerValue ptrval ++ ")"
  | .MVarray mvals => "{" ++ ppMemValueList mvals ++ "}"
  | .MVstruct tag xs =>
    "(struct " ++ ppSymbol tag ++ "){" ++ ppMemValueMembers xs ++ "}"
  | .MVunion tag membrIdent mval =>
    "(union " ++ ppSymbol tag ++ "){." ++ ppIdentifier membrIdent ++ "= "
      ++ stringFromMemValue mval ++ "}"

def ppMemValueList : List MemValue → String
  | [] => ""
  | [mval] => stringFromMemValue mval
  | mval :: rest => stringFromMemValue mval ++ ", " ++ ppMemValueList rest

def ppMemValueMembers : List (identifier × ctype × MemValue) → String
  | [] => ""
  | [(ident, _, mval)] => "." ++ ppIdentifier ident ++ "= " ++ stringFromMemValue mval
  | (ident, _, mval) :: rest =>
    "." ++ ppIdentifier ident ++ "= " ++ stringFromMemValue mval ++ ", "
      ++ ppMemValueMembers rest
end

/-! ## CHERI intrinsics — impl_mem.ml:2175-2191: in the concrete model every
    one is `assert false (* CHERI only *)`. Mirrored as fail-stops with
    the OCaml text (zero-discrepancy Z-22, ruling Q4): the value-returning
    stubs that stood here were the banned fail-OPEN shape (a value where
    the oracle crashes). Reachability: `is_CHERI` is false on the matched
    default switch set and CHERI is a REFUSED mode (Z-24); the elaboration
    emits the CHERI memops/intrinsics only under it, so no matched-mode
    program reaches these. `cheriPointerHashPrintf` has no impl_mem.ml
    counterpart at all (a lem-side target_rep with no OCaml body in the
    concrete model) — fail-stop likewise. -/

def deriveCap (_ : Bool) (_ : derivecap_op) (_ _ : IntegerValue) : IntegerValue :=
  failwithI "assert false (* CHERI only *): Concrete.derive_cap (impl_mem.ml:2175-2176)"
def capAssignValue (_ : CerbLocation.Loc) (_ _ : IntegerValue) : IntegerValue :=
  failwithI "assert false (* CHERI only *): Concrete.cap_assign_value (impl_mem.ml:2178-2179)"
def nullCap (_ : Bool) : IntegerValue :=
  failwithI "assert false (* CHERI only *): Concrete.null_cap (impl_mem.ml:2184-2185)"
def ptrTIntValue (_ : IntegerValue) : IntegerValue :=
  failwithI "assert false (* CHERI only *): Concrete.ptr_t_int_value (impl_mem.ml:2181-2182)"
def cheriPointerHashPrintf (_ : Bool) (_ : PointerValue) : String :=
  failwithI "CHERI only: cheri_pointer_hash_printf has no concrete-model body"
def getIntrinsicTypeSpec (_ : String) : Option intrinsics_signature :=
  failwithI "assert false (* CHERI only *): Concrete.get_intrinsic_type_spec (impl_mem.ml:2187-2188)"

/-! ## Monadic operations -/

abbrev memM (a : Type) := ndM a String mem_error (mem_constraint IntegerValue) MemState

/-- An intentional model stop, distinct from modeled memory errors. -/
def failStopMem {a : Type} (msg : String) : memM a := CerbFail.failStopND msg

/-- A PNVI refusal (`pnviRefusal`) ascribed at the memory MONAD, for the refusals that sit
    inside an `ND fun st => …` body (R-PNVI-08, R-PNVI-10; PNVI arc S4 Part 1, the S3
    review's F1). The failure leaf's kernel default is the `Inhabited (memM a)` instance's,
    `ND fun _ => (NDkilled default, default)` — a KILL — where a `failwithI` at the body's
    pair type `nd_action … × MemState` would default to `(NDactive default, default)`, an
    active result. So these sites are honestly monadic failure sites (the failure census's
    `monadic_ascribed` group, `scripts/failure_census.py`), not pure ones. Use at a site as
    `match pnviRefuseM d with | ND f => f st`. At run time the leaf aborts first, as every
    refusal does (`LEAN_ABORT_ON_PANIC`). -/
def pnviRefuseM {a : Type} (detail : String) : memM a := failwithI (pnviRefusal detail)

def memReturn {a : Type} (x : a) : memM a := nd_return x

/-- The concrete model's kill reason for a memory error — mirrors
    Concrete.fail (impl_mem.ml:540-546): a mem_error that maps to an
    undefined behaviour via `undefinedFromMem_error` (mem_common.lem:248+)
    kills with `Undef0 (loc, [ub])` (→ batch verdict `Undefined {ub:...}`),
    everything else with `Other err`. Default loc mirrors OCaml's
    `?(loc=Cerb_location.other "Concrete")`. -/
def failReason (err : mem_error)
    (loc : CerbLocation.Loc := CerbLocation.other "Concrete") :
    kill_reason mem_error :=
  match undefinedFromMem_error err with
  | some ub => Undef0 loc [ub]
  | none => kill_reason.Other err

/-- fail — impl_mem.ml:540-546 (see failReason). -/
def memFail {a : Type} (err : mem_error)
    (loc : CerbLocation.Loc := CerbLocation.other "Concrete") : memM a :=
  kill (failReason err loc)

/-! ### Exposure and iota — the PNVI provenance state (PNVI arc S2/S3, 2026-10-07)

Mirrors of impl_mem.ml:877-942, written as STATE functions (PNVI arc S3, deviation
D-S3-1 of the S3 record): every caller is a hand-written `ND fun st => …` body, and
four of them (`killM`, `ptrfromint`, `intfromptr`, `eqPtrval`) bind no `[LemFuel]`
— a monadic form over the fuel'd `nd_bind` would add that binder to their
signatures (and a lem `fuel_consumer` declaration, moving the generated Lean and the
consumer's frozen terms) for no behavioural gain. Upstream's own functions only read
or update the state; a precondition's own `fail` (its `get_allocation`) is the
`.error` of an `Except`. Callers: load's `expose_allocations` (:1602-1606),
intfromptr's `expose_allocation` (:2490-2498), ptrfromint's `add_iota` (:2202), the
kill/load/store `Prov_symbolic` arms' `resolve_iota` (:1541, :1683, :1791), and the
`lookup_iota`s of eq/diff/validForDeref/eff_array_shift (:1907, :2038, :2066, :2153,
:2320). Every caller sits behind a `Prov_symbolic` pointer (never minted at the
default switch set) or a PNVI switch test (`false` at `⟨[]⟩` by `rfl`). -/

/-- expose_allocation — impl_mem.ml:877-886 (PNVI-ae): the allocation's taint
    becomes `Exposed`; an absent id is a no-op (`IntMap.update … None -> None`,
    = `Std.TreeMap.modify`). -/
def exposeAllocation (allocId : StorageInstanceId) (st : MemState) : MemState :=
  { st with allocations := st.allocations.modify allocId fun alloc => { alloc with taint := .Exposed } }

/-- expose_allocations — impl_mem.ml:887-901 (PNVI-ae): `NoTaint` → nothing;
    `NewTaint xs` → each id exposed, in list order (absent ids skipped). -/
def exposeAllocations : ProvTaint → MemState → MemState
  | .NoTaint, st => st
  | .NewTaint xs, st =>
    let expose (acc : Std.TreeMap Int Allocation) (allocId : StorageInstanceId) :=
      acc.modify allocId fun alloc => { alloc with taint := .Exposed }
    { st with allocations := xs.foldl expose st.allocations }

/-- add_iota — impl_mem.ml:903-909 (PNVI-ae-udi): a fresh iota (`next_iota`,
    then incremented) mapped to `Double (id1, id2)`. -/
def addIota (allocIds : StorageInstanceId × StorageInstanceId) (st : MemState) :
    SymbolicStorageInstanceId × MemState :=
  let iota := st.nextIota
  (iota, { st with nextIota := st.nextIota + 1
                   iotaMap := st.iotaMap.insert iota (.Double allocIds.1 allocIds.2) })

/-- lookup_iota — impl_mem.ml:911-914 (PNVI-ae-udi): `IntMap.find iota
    st.iota_map`. An iota absent from the map raises `Not_found` upstream (an
    uncaught exception); REFUSED here (design §G.1 row R5, `R-PNVI-04`).
    Unreachable by construction while every `Prov_symbolic` is minted by
    `addIota`, which inserts its key, and nothing removes a key. -/
def lookupIota (st : MemState) (iota : SymbolicStorageInstanceId) : IotaEntry :=
  match st.iotaMap.get? iota with
  | some entry => entry
  | none =>
    failwithI (pnviRefusal s!"R-PNVI-04: lookup_iota, iota {iota} absent from the iota map — impl_mem.ml:912-914 `IntMap.find iota st.iota_map` (raises Not_found)")

/-- The outcome of a `resolve_iota` precondition — impl_mem.ml:917-942
    `[ `OK | `FAIL of Cerb_location.t * mem_error ]` (built by the kill, load and
    store `Prov_symbolic` arms). -/
inductive IotaPrecond where
  | OK
  | FAIL (loc : CerbLocation.Loc) (err : mem_error)

/-- A `resolve_iota` precondition: it reads the state and may itself `fail`
    (upstream's `get_allocation ~loc z`, impl_mem.ml:704-710) — that failure is the
    `.error` and aborts the whole resolution, as upstream's `fail` (a kill) does. -/
abbrev IotaPrecondFn := StorageInstanceId → MemState → Except (kill_reason mem_error) IotaPrecond

/-- resolve_iota — impl_mem.ml:916-942 (PNVI-ae-udi): `Single id` → `precond
    id` must hold (else its failure); `Double (id1, id2)` → `precond id1`, else
    `precond id2`, else the SECOND failure (the error the oracle reports); then
    the iota is collapsed to `Single` of the chosen id (`IntMap.add`). A
    `FAIL (loc, err)` is `fail ~loc err` (`failReason`; `fail` is impl_mem.ml:575
    in this tree). The preconditions run on the state BEFORE the collapse (they
    only read it). -/
def resolveIota (precond : IotaPrecondFn) (iota : SymbolicStorageInstanceId) (st : MemState) :
    Except (kill_reason mem_error) (StorageInstanceId × MemState) :=
  let chosen : Except (kill_reason mem_error) StorageInstanceId :=
    match lookupIota st iota with
    | .Single allocId =>
      match precond allocId st with
      | .error k => .error k
      | .ok .OK => .ok allocId
      | .ok (.FAIL loc err) => .error (failReason err loc)
    | .Double allocId1 allocId2 =>
      match precond allocId1 st with
      | .error k => .error k
      | .ok .OK => .ok allocId1
      | .ok (.FAIL _ _) =>
        match precond allocId2 st with
        | .error k => .error k
        | .ok .OK => .ok allocId2
        | .ok (.FAIL loc err) => .error (failReason err loc)
  match chosen with
  | .error k => .error k
  | .ok allocId => .ok (allocId, { st with iotaMap := st.iotaMap.insert iota (.Single allocId) })

/-- get_allocation ~loc — impl_mem.ml:704-710, inside a precondition: the live
    allocation record, or `fail ~loc (MerrOutsideLifetime …)`. -/
def getAllocationE (loc : CerbLocation.Loc) (st : MemState) (allocId : StorageInstanceId) :
    Except (kill_reason mem_error) Allocation :=
  match st.allocations.get? allocId with
  | some alloc => .ok alloc
  | none => .error (failReason (MerrOutsideLifetime s!"Concrete.get_allocation, alloc_id={allocId}") loc)

/-- `resolveIota` commutes with replacing `last_used`, for a precondition that does not
    read it (every precondition of the kill/load/store arms: `hp` is `rfl` there) — a
    consumer comparing a memory operation on `σ` and on `{ σ with lastUsed := u }` rewrites
    the resolution instead of reducing it (PNVI arc S3; the S3 record's consumer note). -/
theorem resolveIota_lastUsed (p : IotaPrecondFn) (u : Option StorageInstanceId)
    (hp : ∀ z (s : MemState), p z { s with lastUsed := u } = p z s) (iota : SymbolicStorageInstanceId)
    (s : MemState) :
    resolveIota p iota { s with lastUsed := u } =
      (match resolveIota p iota s with
       | .error k => .error k
       | .ok r => .ok (r.1, { r.2 with lastUsed := u })) := by
  have hl : lookupIota { s with lastUsed := u } iota = lookupIota s iota := rfl
  simp only [resolveIota, hl, hp]
  split <;> simp_all

def alignDown (addr align : Nat) : Nat := (addr / align) * align

/-! ### Bytemap operations -/

def writeBytesTo (st : MemState) (addr : Int) (bytes : List AbsByte) : MemState :=
  -- insert-or-replace per byte (was: prepend + filter of the whole map)
  let bm := (bytes.foldl
    (fun (acc : Std.TreeMap Int AbsByte × Int) b => (acc.1.insert acc.2 b, acc.2 + 1))
    (st.bytemap, addr)).1
  { st with bytemap := bm }

/-- Remove a killed allocation's bytes from the bytemap. The allocator's cursor
    only moves down (`allocator`), so no later allocation overlaps
    `[base, base + size)`, and every `loadM` arm requires a live, in-bounds
    allocation before `readBytesFrom`. The erased bytes are therefore never
    read again; keeping them only retains memory (the oracle keeps them). -/
def eraseBytes (st : MemState) (base : Int) (size : Int) : MemState :=
  let bm := (List.range size.toNat).foldl
    (fun (bm : Std.TreeMap Int AbsByte) (i : Nat) => bm.erase (base + (i : Int))) st.bytemap
  { st with bytemap := bm }

def readBytesFrom (st : MemState) (addr : Int) (size : Nat) : List AbsByte :=
  (List.range size).map fun (i : Nat) =>
    match st.bytemap.get? (addr + (i : Int)) with
    | some b => b
    | none => { prov := .Prov_none, copyOffset := none, value := none }

def getAllocation (st : MemState) (pv : PointerValue) : Option (Int × Allocation) :=
  match pv with
  | .PV (.Prov_some allocId) _ =>
    if st.deadAllocations.contains allocId then none
    else (st.allocations.get? allocId).map (fun a => (allocId, a))
  | _ => none

def isInBounds (alloc : Allocation) (addr size : Int) : Bool :=
  addr >= alloc.base && addr + size <= alloc.base + alloc.size

/-! ### Allocation — impl_mem.ml:1288-1435 -/

/-- readonly_status per init_opt — impl_mem.ml:1304-1333: uninitialized
    allocations are IsWritable (:1306); pre-initialized ones (Core
    create_readonly: string literals, const objects) are IsReadOnly with
    the kind chosen by prefix (:1325-1332).
    A NAMED helper (not an inline match in allocateObject, arc-10 S2):
    the extra nested match on `initOpt`/`pref` inside allocateObject's
    already match-heavy body pushed Lean's equation-lemma generation for
    allocateObject past maxRecDepth, breaking downstream
    `simp only [CerbMem.allocateObject]` proofs (found by the since-
    parked reasoning-era equation lemmas). Semantics identical to the
    inline arc-10 S1 form. -/
def readonlyStatusForAlloc (pref : prefix0) (initOpt : Option MemValue) : ReadonlyStatus :=
  match initOpt with
  | none => .IsWritable
  | some _ => .IsReadOnly (match pref with
      | PrefStringLiteral _ _ => readonly_kind.ReadonlyStringLiteral
      | PrefTemporaryLifetime _ _ => readonly_kind.ReadonlyTemporaryLifetime
      | _ => readonly_kind.ReadonlyConstQualified)

/-- Uninitialized allocations are writable (impl_mem.ml:1306); @[simp] so
    downstream closed-run proofs (full-`simp` steps) reduce it without
    naming it. -/
@[simp] theorem readonlyStatusForAlloc_none (pref : prefix0) :
    readonlyStatusForAlloc pref none = .IsWritable := rfl

/-- The allocator's out-of-memory kill — `fail (MerrOther "Concrete.allocator:
    failed (out of memory)")` (impl_mem.ml:1258-1259 and :1263-1264 in this tree;
    the allocator's older per-line comments are −3 from these), NAMED so a
    consumer classifies the outcome by this constant instead of matching the
    string (seam-hygiene H3, 2026-09-19; cerberus-sl's request item 4, interim).
    `mem_error` has no OOM constructor (mem_common.lem:129-132) — a shared-model
    `MerrOutOfMemory` is a separate slice. `allocator_below_request_kills`
    (CerbMemAllocatorProofs.lean) is stated with it. -/
def oomKill : kill_reason mem_error := Other (MerrOther "Concrete.allocator: failed (out of memory)")

/-- allocator — impl_mem.ml:1247-1270, the arithmetic verbatim on Z (Int),
    AFTER remedy 1 of upstream-tray draft 44 (fork fix, 2026-09-16 — the
    fork deviates from pristine `b9aeedcb4` here, OBSERVABLY at upstream's
    own bound: one `malloc` request larger than the cursor by less than
    `align/2` — tests/minimal/112-allocator-exhausted-single-request.c —
    gets `Specified(6)` from pristine and the out-of-memory kill from the
    fork and Lean; register rows, VALIDATION.md §3 "Fork ≠ pristine"):
    `z = last_address - sz` (:1252); `z < 0` → `fail (MerrOther
    "Concrete.allocator: failed (out of memory)")` (:1255-1256 — THE FIX: the
    cursor is below the request, so no rounding may run. Pristine :1254 rounded
    `z - (if q < 0 then -m else m)`, a truncating-division idiom, but
    `Z.quomod = ediv_rem` (impl_mem.ml:9) is EUCLIDEAN — `m ≥ 0` always — so
    for `z < 0` the line ADDED `m` and, for `-align/2 < z < 0`, SUCCEEDED at an
    address in `(0, align)` overlapping the live object at `last_address`
    and misaligned; draft 44 has the verbatim reproductions on both engines);
    then `(_, m) = quomod z align` (:1258) — Lean's Int `%` IS emod.
    `align = 0` RAISES `Division_by_zero` there; Lean fail-stops at the same
    point (a loud kill mirroring the oracle's uncaught exception, never the
    fail-OPEN `.max 1` clamp that stood here; [USER 2026-10-03] "fall back to
    loudly rejecting (either as unsupported, or matching upstream)",
    docs/2026-10-03_total-arith-and-bookkeeping-record.md); it sits where the
    OCaml's quomod sits — AFTER the `z < 0` kill. Its one former C route,
    `aligned_alloc(0, 0)`, now stops earlier, at std.core:385's `0 rem_t 0`,
    exactly as the oracle does (Z2-M-01, `integerRem_t`), so the arm is
    defensive; `z' = z - m` (:1259, a plain align-down: the
    `q < zero` branch is dead and deleted); `z' ≤ 0` → the same out-of-memory
    fail (:1260-1261; text mirrored — zero-discrepancy Z2-M-03); else
    `next_alloc_id` bumped, `last_used = Some alloc_id`, `last_address = addr`
    (:1264-1270). The VIP twin (memory/vip/impl_mem.ml:202-225) carries the
    same text.
    CONTRACT — kernel theorem `CerbMem.allocator_active_sound`
    (CerbMemAllocatorProofs.lean): an ACTIVE result `a` has `align ∣ a`,
    `0 < a`, `a + sz ≤ st.lastAddress` (its end at or below the cursor —
    disjoint from everything at or above it, for `sz ≥ 0`), and the new
    cursor is `a`; the
    below-the-request regime is `allocator_below_request_kills`. Runtime
    witness: `test/Unit/AllocatorSoundnessTest.lean` (the four draft-44
    states, with the pre-fix values as the negative control).
    Zero-discrepancy Z-13 / Z2-M-05: the two callers used to clamp
    size and align with `.max 1` and map a negative size to 0 through
    `.toNat` — silent normalisations the OCaml has nowhere; both gone. -/
def allocator (sz align : Int) : memM (StorageInstanceId × Address) :=
  ND fun st =>
    let allocId := st.nextAllocId
    let z := st.lastAddress - sz                                                 -- :1252
    if z < 0 then                                                                -- :1255-1256 (draft 44 fix)
      (NDkilled oomKill, st)
    else if align == 0 then                                                      -- :1258 quomod → Division_by_zero
      (NDkilled (CerbFail.failStopKill "CerbMem.allocator: alignment 0 has no meaning in the model (impl_mem.ml:1258 quomod raises Division_by_zero — mirrored as a fail-stop; docs/2026-10-03_total-arith-and-bookkeeping-record.md)"), st)
    else
      let m := z % align                                                         -- :1258 (Euclidean remainder, m ≥ 0)
      let z' := z - m                                                            -- :1259 (align down)
      if z' ≤ 0 then                                                             -- :1260-1261
        (NDkilled oomKill, st)
      else                                                                       -- :1263-1270
        (NDactive (allocId, z'),
         { st with nextAllocId := allocId + 1, lastUsed := some allocId, lastAddress := z' })

/-- allocate_object — impl_mem.ml:1288-1347. `size = sizeof ty` (:1289, no
    clamp); `req_addr_opt = Some _` → `failwith "TODO: cerb::with_address()
    is yet implemented"` (:1293-1295) — mirrored as a fail-stop (zero-
    discrepancy Z-14: the argument was silently ignored; reachable only via
    the fork-only `cerb::with_address` attribute, never on upstream inputs);
    then `allocator size align`. `init_opt = None` (:1303-1319): a writable
    allocation with `ty = Some ty`, and the bytemap receives `repr
    (MVunspecified ty)` = sizeof padding bytes (:1315-1319; the
    `SW_zero_initialised` arm :1308-1314 is switch-conditioned, the switch
    set is refused — Z-24 — so the default arm is the only reachable one).
    `init_opt = Some mval` (:1320-1345): readonly kind by prefix
    (`readonlyStatusForAlloc`), `repr` threading the funptrmap. -/
def allocateObject [LemFuel] [CerbGlobal.Switches] (enumDefs : EnumDefs) (tagDefs : TagDefs) (_ : Nat) (pref : prefix0) (alignIv : IntegerValue)
    (ty : ctype) (reqAddrOpt : Option Int) (initOpt : Option MemValue) : memM PointerValue :=
  match alignIv with
  | .IV _ alignN =>
  let size : Int := sizeofCtype enumDefs tagDefs ty                                       -- :1289
  match reqAddrOpt with
  | some _ => failStopMem "TODO: cerb::with_address() is yet implemented"           -- :1293-1295
  | none =>
  nd_bind (allocator size alignN) fun (idAddr : StorageInstanceId × Address) =>  -- :1291-1292
  let (allocId, addr) := idAddr
  ND fun st =>
    -- :1318-1324 SW_zero_initialised (the `None` init branch's bytemap choice) →
    -- zero-filled bytes. Refused set (Z-24): the default arm (:1325-1329 repr of
    -- MVunspecified, below) is the only reachable one; the set case is loud
    -- (seam-hygiene H2). The guard is that branch's test, `init_opt = None ∧
    -- has_switch`, hoisted in front of the unchanged body.
    if initOpt.isNone && CerbGlobal.has_switch .zero_initialised then
      (NDkilled (Other (MerrOther "allocateObject: SW_zero_initialised is set but the zero-fill arm (impl_mem.ml:1318-1324) is not ported — switches are refused (Z-24)")), st)
    else
    -- readonly_status per init_opt — impl_mem.ml:1304-1333 (see
    -- readonlyStatusForAlloc above)
    let alloc : Allocation := { base := addr, size := size, ty := some ty,
                                isReadonly := readonlyStatusForAlloc pref initOpt,
                                prefix_ := pref }
    let st' := { st with allocations := st.allocations.insert allocId alloc }
    let st' := match initOpt with
      | some val_ =>
        -- repr threads the funptrmap into the state — impl_mem.ml:1336-1344
        let (fpm, bs) := memValueToBytes enumDefs tagDefs st'.funptrmap val_
        writeBytesTo { st' with funptrmap := fpm } addr bs
      | none =>
        -- :1315-1319 `repr st.funptrmap (MVunspecified ty)` (funptrmap
        -- result discarded, `let (_, pre_bs)`)
        let (_, bs) := memValueToBytes enumDefs tagDefs st'.funptrmap (.MVunspecified ty)
        writeBytesTo st' addr bs
    (NDactive (.PV (.Prov_some allocId) (.PVconcrete none addr)), st')

/-- allocate_region — impl_mem.ml:1420-1435: `allocator size_n align_n`
    (:1421, no clamp, a negative size flows through the Z arithmetic —
    Allocation.size is Int here too), then the allocation record with
    `prefix= Symbol.PrefMalloc` UNCONDITIONALLY (:1429; the `pref`
    argument is unused, `:1428 (* TODO: why aren't we using the argument
    pref? *)` — zero-discrepancy Z-15: this stored the caller's prefix),
    `ty= None`, `is_readonly= IsWritable`; `dynamic_addrs` gains the base
    (:1433). NO bytemap write (zero-discrepancy Z2-M-04): `fetch_bytes`
    (:708-722) defaults an absent byte to `AbsByte.v Prov_none None`,
    exactly as `readBytesFrom` does here — the eager `List.replicate size`
    materialisation that stood here was behaviour-preserving and the
    one-line cause of the Z-30 malloc OOM class
    (tests/z2-probes/mem/malloc_oom_msg.c). -/
def allocateRegion [LemFuel] (_ : Nat) (_pref : prefix0) (alignIv sizeIv : IntegerValue) : memM PointerValue :=
  match alignIv, sizeIv with
  | .IV _ alignN, .IV _ sizeN =>
  nd_bind (allocator sizeN alignN) fun (idAddr : StorageInstanceId × Address) =>   -- :1421
  let (allocId, addr) := idAddr
  ND fun st =>
    let alloc : Allocation := { base := addr, size := sizeN, ty := none,
                                isReadonly := .IsWritable, prefix_ := PrefMalloc }  -- :1429
    (NDactive (.PV (.Prov_some allocId) (.PVconcrete none addr)),
     { st with allocations := st.allocations.insert allocId alloc,
               dynamicAddrs := addr :: st.dynamicAddrs })                            -- :1430-1434

/-! ### Kill — impl_mem.ml:1464-1550 (zero-discrepancy Z-07/Z-08/Z-10, noodle
    D6/D7; the arms and their ORDER mirror `kill loc is_dyn` exactly — the
    charter's Z-09/Z-11/Z-12 seam rows fall inside the same hunk) -/

def killM [CerbGlobal.Switches] (loc : CerbLocation.Loc) (isDynamic : Bool) (pv : PointerValue) : memM Unit :=
  ND fun st =>
    -- every `fail ~loc` routes through the fail mapping (impl_mem.ml:540-546):
    -- Free_non_matching/Free_dead_allocation → UB179a/UB179b, MerrOther and
    -- Free_out_of_bound → Other (a batch Error line, not UB)
    let fail_ (err : mem_error) := (NDkilled (failReason err loc), st)
    match pv with
    | .PV _ (.PVnull _) =>
      -- :1465-1469 — NOT conditional on is_dyn: a null kill succeeds unless
      -- SW_forbid_nullptr_free is set (that switch is refused, Z-24)
      if CerbGlobal.has_switch .forbid_nullptr_free then fail_ MerrFreeNullPtr
      else (NDactive (), st)
    | .PV _ (.PVfunction _) =>
      fail_ (MerrOther "attempted to kill with a function pointer")             -- :1470-1471
    | .PV .Prov_none (.PVconcrete _ _) =>
      fail_ (MerrOther "attempted to kill with a pointer lacking a provenance")  -- :1472-1473
    | .PV .Prov_device (.PVconcrete _ _) =>
      (NDactive (), st)                                                          -- :1474-1476 ("TODO: should that be an error ??")
    | .PV (.Prov_symbolic iota) (.PVconcrete _ addr) =>
      -- impl_mem.ml:1518-1553 (PNVI-ae-udi; THIS tree's lines), in upstream's
      -- order: the dynamic check `is_dynamic addr` (:1531-1539), then
      -- `resolve_iota precondition iota` (:1541) with the precondition
      -- :1520-1529 — dead → `Free_dead_allocation` WHATEVER `is_dyn` (unlike the
      -- Prov_some arm's static `failwith`), else `get_allocation ~loc z`, then
      -- `addr = alloc.base` or `Free_out_of_bound` — then the retirement
      -- :1545-1549 and the zap switch :1550-1553 (refused set, loud exactly as in
      -- the Prov_some arm below). Reached only through a `Prov_symbolic` pointer,
      -- which nothing mints at the default switch set (ptrfromint's PNVI arm).
      let precondition : IotaPrecondFn := fun z s =>
        if s.deadAllocations.contains z then .ok (.FAIL loc (MerrUndefinedFree Free_dead_allocation))
        else match getAllocationE loc s z with
          | .error k => .error k
          | .ok alloc =>
            if addr == alloc.base then .ok .OK
            else .ok (.FAIL loc (MerrUndefinedFree Free_out_of_bound))
      if isDynamic && !st.dynamicAddrs.contains addr then
        fail_ (MerrUndefinedFree Free_non_matching)                              -- :1534-1535
      else match resolveIota precondition iota st with
        | .error k => (NDkilled k, st)
        | .ok (allocId, st1) =>
          let st1' := match st1.allocations.get? allocId with
            | some alloc => eraseBytes st1 alloc.base alloc.size
            | none => st1
          let st' := { st1' with
            deadAllocations := st1'.deadAllocations.insert allocId
            lastUsed := some allocId
            allocations := st1'.allocations.erase allocId }
          if CerbGlobal.has_switch .zap_dead_pointers then
            (NDkilled (Other (MerrOther "killM: SW_zap_dead_pointers is set but zap_pointers (impl_mem.ml:1447-1462) is not ported — switches are refused (Z-24)")), st)
          else (NDactive (), st')
    | .PV (.Prov_some allocId) (.PVconcrete _ addr) =>
      -- :1515-1549 in THIS order: is_dynamic addr (the POINTER's address, not
      -- alloc.base) → is_dead → get_allocation → addr = alloc.base
      if isDynamic && !st.dynamicAddrs.contains addr then
        fail_ (MerrUndefinedFree Free_non_matching)                              -- :1518-1525
      else if st.deadAllocations.contains allocId then
        if isDynamic then fail_ (MerrUndefinedFree Free_dead_allocation)         -- :1529-1530
        else
          -- :1531-1532 `failwith "Concrete: FREE was called on a dead allocation"`
          -- — an UNCAUGHT exception on the oracle (exit 125), mirrored as a
          -- fail-stop carrying the OCaml text (Q4 ruling, charter §7; Z-10).
          -- REACHABILITY: a static (scope-exit) kill finds its allocation dead
          -- only after an ACCEPTED wrong free of the same object — i.e. only
          -- through the tray-19 dynamic_addrs address-keying defect (Z-77: a
          -- zero-size `alloc` minted at a live object's base; dynamic-addrs
          -- record rows k/n', witnessed on both oracles as this failwith and
          -- on Lean via libc-body injection) or the fork-only
          -- `cerb::with_address` attribute. Unreachable from C through
          -- malloc/free (argument temporaries, translation.lem:4435).
          (NDkilled (CerbFail.failStopKill "Concrete: FREE was called on a dead allocation"), st)
      else match st.allocations.get? allocId with
        | none =>
          -- :1534 get_allocation ~loc → :669-675 MerrOutsideLifetime (UB009)
          fail_ (MerrOutsideLifetime s!"Concrete.get_allocation, alloc_id={allocId}")
        | some alloc =>
          if addr == alloc.base then                                             -- :1535-1546
            let stE := eraseBytes st alloc.base alloc.size
            let st' := { stE with
              deadAllocations := stE.deadAllocations.insert allocId
              lastUsed := some allocId                                             -- :1541
              allocations := stE.allocations.erase allocId }
            -- :1543-1546 SW_zap_dead_pointers → zap_pointers (:1447-1462, not
            -- ported): that switch is refused (Z-24), so the OCaml default
            -- arm `return ()` is the only reachable one; the set case is loud
            if CerbGlobal.has_switch .zap_dead_pointers then
              (NDkilled (Other (MerrOther "killM: SW_zap_dead_pointers is set but zap_pointers (impl_mem.ml:1447-1462) is not ported — switches are refused (Z-24)")), st)
            else (NDactive (), st')
          else fail_ (MerrUndefinedFree Free_out_of_bound)                       -- :1547-1548

/-! ### Load / Store — impl_mem.ml:1552-1789

    The provenance case split mirrors OCaml's load/store matches
    (impl_mem.ml:1604-1664 / 1711-1789). Notably (survey finding 12) the
    OCaml concrete model NEVER emits the NoProvPtr constructor — the
    three distinct outcomes are:
      Prov_none            → MerrAccess _ OutOfBoundPtr
                             (impl_mem.ml:1609-1610 / 1716-1717)
      Prov_some + dead     → load: MerrAccess LoadAccess DeadPtr
                             (explicit is_dead check, impl_mem.ml:1645-1650);
                             store: NO dead check — is_within_bound's
                             get_allocation on a discarded allocation
                             fails MerrOutsideLifetime
                             (impl_mem.ml:1763 → :669-675)
      Prov_some + missing  → MerrOutsideLifetime (get_allocation,
                             impl_mem.ml:669-675)
    Every failure goes through the fail mapping (failReason,
    impl_mem.ml:540-546), so UB-classed errors surface as Undef0.
      Prov_device            → is_within_device (deviceRanges, impl_mem.ml:620-624)
                             ? do_load/do_store : OutOfBoundPtr (:1611-1617,
                             :1718-1724) — zero-discrepancy Z-06 (noodle D5);
                             this file used to assert the ranges were empty
      Prov_symbolic          → resolve_iota with the arm's precondition, then
                             do_load/do_store on the resolved allocation
                             (impl_mem.ml:1662-1684 / :1771-1804 in THIS tree;
                             PNVI arc S3) — reached only through a pointer that
                             ptrfromint's PNVI arm minted, never at the default
                             switch set.

    PORTED IN THE EXPLICIT SHAPE (seam-hygiene H2, 2026-09-19,
    docs/2026-09-18_seam-hygiene-record.md §4; formerly DECLARED as
    zero-discrepancy Z2-M-20 — Z2 record 2026-09-04 row Z2-M-20) — every
    SWITCH-CONDITIONED arm of impl_mem.ml is written here as
    `if CerbGlobal.has_switch … then <loud kill> else <the default arm>`:
    every switch these arms read is REFUSED by this port (Z-24, VALIDATION.md §3
    "(c) Semantics switches"; since PNVI arc S4, 2026-10-07, the one accepted set is
    `[.PNVI .AE_UDI]`, under which each of these guards is still `false` except the
    `is_PNVI` disjunct below, a real arm since S3), so on the matched default set (`Switches.set []`,
    main.ml:129-143; since PNVI arc S1, 2026-10-05, every read is of the
    instance-implicit parameter `[CerbGlobal.Switches]`, which each function
    here binds after `[LemFuel]`, and the run's instance is Main.lean's
    `⟨CerbGlobal.defaultSwitches⟩` = `⟨[]⟩`, at which every `has_switch … = false`
    and `is_PNVI () = false` by `rfl` — CerbGlobal.lean's `has_switch_*_default`
    lemmas) each guard reduces to its default arm — the
    only arm either engine executes — and a consumer's proof rewrites with
    the lemma instead of trusting a comment; the SET branch is a loud kill
    naming the un-ported OCaml arm (never reachable while those switches are
    refused; hermetic pin: test/Unit/OpaqueFailureTest.lean). Permissive pointer
    arithmetic is now ported and selectable with PNVI-ae-udi. The arms, at
    THIS tree's impl_mem.ml lines: `SW_strict_pointer_equality` (eq_ptrval
    :1860 → eqPtrval), `SW_strict_pointer_relationals` (lt/gt/le/ge_ptrval
    :1897/:1915/:1930/:1947 → lt/gt/le/gePtrval), `SW_pointer_arith
    PERMISSIVE` (diff_ptrval :1978 → diffPtrval), `SW_pointer_arith STRICT`
    ∨ (`is_PNVI` ∧ ¬PERMISSIVE) (eff_array_shift_ptrval :2345-2346 Prov_some,
    :2357-2358 Prov_none → effArrayShiftPtrval), `SW_forbid_nullptr_free`
    (kill :1474 → killM), `SW_zap_dead_pointers` (kill :1518/:1552 → killM),
    `SW_zero_initialised` (allocate_object :1318 → allocateObject),
    `SW_strict_reads` (load :1601 → loadM). The per-arm `:NNNN` comments
    elsewhere in this file predate the part-one +8 line shift of impl_mem.ml.
    PNVI arc S3 (2026-10-07): the PNVI tests are NOT loud kills any more —
    they select the REAL arms, mirrored with this tree's impl_mem.ml lines:
    ptrfromint's `is_PNVI ()` arm, intfromptr's and load's
    `SW_PNVI AE ∨ AE_UDI` exposure arms, and the `is_PNVI ∧ ¬PERMISSIVE`
    disjunct of eff_array_shift_ptrval's bounds guard (its `STRICT` disjunct
    stays a loud kill); each is `false` at the default set by `rfl`. -/

/-- device_ranges — impl_mem.ml:620-624, verbatim: two hard-coded ranges
    ("to match the Charon tests"; each 4 bytes). An integer in a range casts
    to a `Prov_device` pointer (ptrfromint :2165-2167) whose loads/stores
    and kills succeed. Zero-discrepancy Z-06: the previous comments here
    claimed the list was empty in this pipeline — false; the oracle's
    behaviour is mirrored (if judged an upstream artefact it is a tray
    question, never a silent Lean deviation). -/
def deviceRanges : List (Int × Int) :=
  [(0x40000000, 0x40000004), (0xABC, 0xAC0)]

/-- is_within_device — impl_mem.ml:681-686. -/
def isWithinDevice [LemFuel] (enumDefs : EnumDefs) (tagDefs : TagDefs) (ty : ctype) (addr : Int) : Bool :=
  deviceRanges.any (fun (lo, hi) => lo ≤ addr && addr + (sizeofCtype enumDefs tagDefs ty : Int) ≤ hi)

/-- is_atomic_member_access — impl_mem.ml:689-706: accessing a PART of an
    atomic allocation (not the whole object with the same type) is an
    AtomicMemberof error. INSTRUMENT note (zero-discrepancy Z2-M-17): the
    OCaml additionally prints two diagnostic lines on the TOOL's stderr
    (:698-702 `addr: … <--> alloc.base: …` / `|lvalue_ty|: … <--> |alloc|:
    …`) — the tool stream, not the program's `stderr:` verdict field; not
    mirrored (tests/z2-probes/mem/atomic_member_stderr.c: identical
    UB042 verdict lines on all three engines). -/
def isAtomicMemberAccess [LemFuel] (enumDefs : EnumDefs) (tagDefs : TagDefs) (alloc : Allocation) (lvalueTy : ctype) (addr : Int) : Bool :=
  match alloc.ty with
  | some allocTy =>
    match allocTy with
    | Ctype _ (.Atomic _) =>
      -- impl_mem.ml:692-703 (the type-equality conjunct deals with a
      -- padding-free first member)
      !(addr == alloc.base && (sizeofCtype enumDefs tagDefs lvalueTy : Int) == alloc.size
        && ctypeEqual lvalueTy allocTy)
    | _ => false
  | none => false

/-- load's PNVI exposure arm — impl_mem.ml:1602-1606 (THIS tree): `if has_switch
    (SW_PNVI `AE) || has_switch (SW_PNVI `AE_UDI) then expose_allocations taint else
    return ()`, as a state function (PNVI arc S3). -/
def exposeOnLoad [CerbGlobal.Switches] (taint : ProvTaint) (st : MemState) : MemState :=
  if CerbGlobal.has_switch (.PNVI .AE) || CerbGlobal.has_switch (.PNVI .AE_UDI) then
    exposeAllocations taint st
  else st

/-- At the default switch set the exposure arm is the identity. -/
theorem exposeOnLoad_default (taint : ProvTaint) (st : MemState) :
    @exposeOnLoad ⟨CerbGlobal.defaultSwitches⟩ taint st = st := rfl

/-- The same at any instance whose switch list is the default (a consumer's own instance,
    `h := rfl`). -/
theorem exposeOnLoad_of_default [inst : CerbGlobal.Switches]
    (h : inst.switches = CerbGlobal.defaultSwitches) (taint : ProvTaint) (st : MemState) :
    exposeOnLoad taint st = st := by
  cases inst with
  | mk sws =>
    obtain rfl : sws = CerbGlobal.defaultSwitches := h
    rfl

/-- Exposure (allocations) and `last_used` touch disjoint fields: the order in which
    `loadM` applies them is immaterial (upstream: expose, then `last_used`). -/
theorem exposeOnLoad_lastUsed [CerbGlobal.Switches] (taint : ProvTaint) (st : MemState)
    (u : Option StorageInstanceId) :
    exposeOnLoad taint { st with lastUsed := u } = { exposeOnLoad taint st with lastUsed := u } := by
  unfold exposeOnLoad
  split <;> (try cases taint) <;> rfl

def loadM [LemFuel] [CerbGlobal.Switches] (enumDefs : EnumDefs) (tagDefs : TagDefs) (loc : CerbLocation.Loc) (ty : ctype) (pv : PointerValue) : memM (Footprint × MemValue) :=
  ND fun st =>
    let fail_ (err : mem_error) := (NDkilled (failReason err loc), st)
    -- do_load — impl_mem.ml:1596-1647 in THIS tree, run on the state it is
    -- given (`get >>= fun st`, :1597): `st` itself on the Prov_device and
    -- Prov_some arms, the post-`resolve_iota` state on the Prov_symbolic arm
    -- (PNVI arc S3). Order, as upstream: fetch + abst (:1599-1600), then the
    -- PNVI `expose_allocations taint` (:1602-1606), then the receipt and
    -- `last_used= alloc_id_opt` (:1607-1609; Z2-M-16), then the _Bool trap check
    -- (:1619-1631), then SW_strict_reads (:1634-1640, the EXPLICIT
    -- `if has_switch .strict_reads then <loud kill> else …` guard, seam-hygiene H2)
    let doLoad (st0 : MemState) (allocOpt : Option StorageInstanceId) (addr : Int) :=
      let size := sizeofCtype enumDefs tagDefs ty
      let bytes := readBytesFrom st0 addr size
      let fp : Footprint := .FP .R addr size
      -- abst at the load address with last_used_union_members and
      -- funptrmap — impl_mem.ml:1600 in THIS tree (the `:NNNN` cites of this
      -- function's other comments are the older numbering, see the header):
      -- the full `abst` — switch set, the `find_overlaping st` closure, the taint
      let r := reconstructValueAbst enumDefs tagDefs (findOverlapping st0) st0.lastUsedUnionMembers st0.funptrmap addr ty bytes
      let mv := r.2
      -- :1602-1606 `expose_allocations taint` under `PNVI AE ∨ AE_UDI`
      -- (`exposeOnLoad`), BEFORE the receipt (F3 of the S2 review). Deliberate
      -- placement divergence, proved equal: upstream exposes and THEN sets
      -- `last_used`; here `last_used` is set first and the exposure applied to that
      -- state — the two touch disjoint fields (`exposeOnLoad_lastUsed`), and the
      -- exposure stays a single call on a variable-sourced update, so unfolding
      -- `loadM` does not copy it into every field. At the default set
      -- `exposeOnLoad t s = s` (`exposeOnLoad_default`, `rfl`): the pre-S3 state.
      let loadedState := recordAccess loc LoadAccess ty pv allocOpt addr bytes mv none
        (exposeOnLoad r.1 { st0 with lastUsed := allocOpt })
      -- trap representation for _Bool — impl_mem.ml:1576-1591
      let isBool := match ty with | Ctype _ (.Basic (.Integer .Bool0)) => true | _ => false
      let isTrap := isBool && match mv with
        | .MVinteger _ (.IV _ n) => n != 0 && n != 1
        | .MVunspecified _ => true
        | _ => false
      -- do_load updates last_used BEFORE the trap check. A failed read
      -- returns that completed-operation state (SC WP0 / review RR2).
      if isTrap then
        (NDkilled (failReason (MerrTrapRepresentation LoadAccess) loc), loadedState)
      -- :1601-1606 SW_strict_reads → MerrReadUninit on an unspecified value.
      -- Refused set (Z-24): the default arm is the only reachable one; the set
      -- case is loud (seam-hygiene H2)
      else if CerbGlobal.has_switch .strict_reads then
        (NDkilled (Other (MerrOther "loadM: SW_strict_reads is set but the strict-reads arm (impl_mem.ml:1601-1606) is not ported — switches are refused (Z-24)")), st0)
      else (NDactive (fp, mv), loadedState)
    match pv with
    | .PV _ (.PVnull _) => fail_ (MerrAccess LoadAccess NullPtr)          -- impl_mem.ml:1605-1606
    | .PV _ (.PVfunction _) => fail_ (MerrAccess LoadAccess FunctionPtr)  -- impl_mem.ml:1607-1608
    | .PV .Prov_none _ => fail_ (MerrAccess LoadAccess OutOfBoundPtr)     -- impl_mem.ml:1609-1610
    | .PV .Prov_device (.PVconcrete _ addr) =>
      -- impl_mem.ml:1611-1617: is_within_device → do_load None addr
      if isWithinDevice enumDefs tagDefs ty addr then doLoad st none addr
      else fail_ (MerrAccess LoadAccess OutOfBoundPtr)
    | .PV (.Prov_symbolic iota) (.PVconcrete _ addr) =>
      -- impl_mem.ml:1662-1684 (PNVI-ae-udi; THIS tree's lines): `resolve_iota
      -- precondition iota >>= fun alloc_id -> do_load (Some alloc_id) addr`, the
      -- precondition :1666-1682 being the Prov_some arm's checks in its order —
      -- dead → DeadPtr; `is_within_bound ~loc z ty addr` (its `get_allocation`
      -- may fail) → OutOfBoundPtr; `is_atomic_member_access` → AtomicMemberof.
      -- Reached only through a `Prov_symbolic` pointer, which nothing mints at
      -- the default switch set (ptrfromint's PNVI arm).
      let precondition : IotaPrecondFn := fun z s =>
        if s.deadAllocations.contains z then .ok (.FAIL loc (MerrAccess LoadAccess DeadPtr))
        else match getAllocationE loc s z with
          | .error k => .error k
          | .ok alloc =>
            if !isInBounds alloc addr (sizeofCtype enumDefs tagDefs ty) then
              .ok (.FAIL loc (MerrAccess LoadAccess OutOfBoundPtr))
            else if isAtomicMemberAccess enumDefs tagDefs alloc ty addr then
              .ok (.FAIL loc (MerrAccess LoadAccess AtomicMemberof))
            else .ok .OK
      match resolveIota precondition iota st with
      | .error k => (NDkilled k, st)
      | .ok (allocId, st1) => doLoad st1 (some allocId) addr
    | .PV (.Prov_some allocId) (.PVconcrete _ addr) =>
      -- impl_mem.ml:1644-1664
      if st.deadAllocations.contains allocId then
        fail_ (MerrAccess LoadAccess DeadPtr)                             -- impl_mem.ml:1645-1650
      else match st.allocations.get? allocId with
        | none =>
          -- get_allocation (via is_within_bound) — impl_mem.ml:669-675
          fail_ (MerrOutsideLifetime s!"Concrete.get_allocation, alloc_id={allocId}")
        | some alloc =>
          if !isInBounds alloc addr (sizeofCtype enumDefs tagDefs ty) then
            fail_ (MerrAccess LoadAccess OutOfBoundPtr)                   -- impl_mem.ml:1651-1656
          else if isAtomicMemberAccess enumDefs tagDefs alloc ty addr then
            fail_ (MerrAccess LoadAccess AtomicMemberof)                  -- impl_mem.ml:1658-1660
          else doLoad st (some allocId) addr

def storeM [LemFuel] (enumDefs : EnumDefs) (tagDefs : TagDefs) (loc : CerbLocation.Loc) (ty : ctype) (isLocking : Bool) (pv : PointerValue) (mv : MemValue) : memM Footprint :=
  ND fun st =>
    let fail_ (err : mem_error) := (NDkilled (failReason err loc), st)
    -- select_ro_kind — impl_mem.ml:1704-1710
    let selectRoKind : prefix0 → readonly_kind := fun pref =>
      match pref with
      | PrefTemporaryLifetime _ _ => readonly_kind.ReadonlyTemporaryLifetime
      | PrefStringLiteral _ _ => readonly_kind.ReadonlyStringLiteral
      | _ => readonly_kind.ReadonlyConstQualified
    -- do_store — impl_mem.ml:1683-1703: bytemap write threads the
    -- funptrmap from repr; then the last_used_union_members update iff
    -- the pointer is PVconcrete (Some membr, _) (union member_shift,
    -- impl_mem.ml:1694-1701)
    -- `allocOpt` is the OCaml `alloc_id_opt`: None on the device path
    -- (:1723 `do_store None addr`), so no is_locking readonly update there.
    -- `st0` is the state do_store runs on (`update begin fun st -> …`): `st` on
    -- the Prov_device and Prov_some arms, the post-`resolve_iota` state on the
    -- Prov_symbolic arm (PNVI arc S3)
    let doStore (st0 : MemState) (allocOpt : Option (Int × Allocation)) (unionMem : Option identifier) (addr : Int) :=
      let (fpm, bytes) := memValueToBytes enumDefs tagDefs st0.funptrmap mv
      let st' := writeBytesTo { st0 with funptrmap := fpm } addr bytes
      let st' := match unionMem with
        | some membr => { st' with lastUsedUnionMembers :=
            (addr, membr) :: st'.lastUsedUnionMembers.filter (fun (a, _) => a != addr) }
        | none => st'
      -- is_locking — impl_mem.ml:1776-1787: readonly kind from the
      -- allocation's prefix
      let st' := match allocOpt with
        | some (allocId, alloc) =>
          if isLocking then
            { st' with allocations := st'.allocations.map fun (id : Int) (a : Allocation) =>
                if id == allocId then
                  { a with isReadonly := .IsReadOnly (selectRoKind alloc.prefix_) }
                else a }
          else st'
        | none => st'
      let fp : Footprint := .FP .W addr (sizeofCtype enumDefs tagDefs ty)
      -- Deliberate placement divergence (skeptical review F6, 2026-09-26): impl_mem.ml records the
      -- store receipt inside its first `update`, BEFORE the union/read-only bookkeeping; here it is
      -- appended AFTER. Same bytes, value, pointer and allocation on both sides; the bookkeeping
      -- touches other fields, so the final states are equal (row 13 compares them).
      (NDactive fp, recordAccess loc StoreAccess ty pv (allocOpt.map Prod.fst)
        addr bytes mv (some isLocking)
        { st' with lastUsed := allocOpt.map Prod.fst })                 -- :1687 last_used
    -- ill-typed-store guard — impl_mem.ml:1673-1681: checked BEFORE the
    -- provenance/pointer-kind match (so it wins over NullPtr etc.);
    -- OCaml's diagnostic printfs (:1674-1680) are not mirrored, the
    -- failure is (MerrOther, non-UB → Other kill, batch Error line).
    if !(ctypeMemCompatible ty (typeofMval mv)) then
      fail_ (MerrOther "store with an ill-typed memory value")
    else
    match pv with
    | .PV _ (.PVnull _) => fail_ (MerrAccess StoreAccess NullPtr)          -- impl_mem.ml:1712-1713 (order per :1711-1717)
    | .PV _ (.PVfunction _) => fail_ (MerrAccess StoreAccess FunctionPtr)  -- impl_mem.ml:1714-1715
    | .PV .Prov_none _ => fail_ (MerrAccess StoreAccess OutOfBoundPtr)     -- impl_mem.ml:1716-1717
    | .PV .Prov_device (.PVconcrete unionMem addr) =>
      -- impl_mem.ml:1718-1724: is_within_device → do_store None addr
      if isWithinDevice enumDefs tagDefs ty addr then doStore st none unionMem addr
      else fail_ (MerrAccess StoreAccess OutOfBoundPtr)
    | .PV (.Prov_symbolic iota) (.PVconcrete unionMem addr) =>
      -- impl_mem.ml:1771-1804 (PNVI-ae-udi; THIS tree's lines): `resolve_iota
      -- precondition iota` (:1791), the precondition :1775-1789 being the Prov_some
      -- arm's checks in its order — `is_within_bound ~loc z ty addr` (its
      -- `get_allocation` may fail; NO dead check on the store path) →
      -- OutOfBoundPtr; read-only → MerrWriteOnReadOnly kind; atomic member →
      -- `MerrAccess (LoadAccess, AtomicMemberof)` (upstream's LoadAccess tag on a
      -- store, :1787 — the same quirk as the Prov_some arm, mirrored); then
      -- `do_store (Some alloc_id) addr` and the is_locking update (:1792-1802).
      -- Reached only through a `Prov_symbolic` pointer, which nothing mints at
      -- the default switch set (ptrfromint's PNVI arm).
      let precondition : IotaPrecondFn := fun z s =>
        match getAllocationE loc s z with
        | .error k => .error k
        | .ok alloc =>
          if !isInBounds alloc addr (sizeofCtype enumDefs tagDefs ty) then
            .ok (.FAIL loc (MerrAccess StoreAccess OutOfBoundPtr))
          else match alloc.isReadonly with
            | .IsReadOnly kind => .ok (.FAIL loc (MerrWriteOnReadOnly kind))
            | .IsWritable =>
              if isAtomicMemberAccess enumDefs tagDefs alloc ty addr then
                .ok (.FAIL loc (MerrAccess LoadAccess AtomicMemberof))
              else .ok .OK
      match resolveIota precondition iota st with
      | .error k => (NDkilled k, st)
      | .ok (allocId, st1) =>
        match st1.allocations.get? allocId with
        | some alloc => doStore st1 (some (allocId, alloc)) unionMem addr
        | none =>
          -- unreachable: the precondition's `get_allocation` found `allocId` in
          -- the same allocation map (`resolveIota` writes only `iotaMap`); loud,
          -- never absorbed
          (NDkilled (CerbFail.failStopKill s!"storeM: the allocation {allocId} resolved for a Prov_symbolic store is absent (unreachable: resolveIota's precondition found it in the same allocation map)"), st)
    | .PV (.Prov_some allocId) (.PVconcrete unionMem addr) =>
      -- impl_mem.ml:1762-1789: NO is_dead check on the store path — a
      -- dead allocation is caught by is_within_bound's get_allocation
      -- (MerrOutsideLifetime); bounds are checked BEFORE readonly
      match st.allocations.get? allocId with
      | none =>
        fail_ (MerrOutsideLifetime s!"Concrete.get_allocation, alloc_id={allocId}")
      | some alloc =>
        if !isInBounds alloc addr (sizeofCtype enumDefs tagDefs ty) then
          fail_ (MerrAccess StoreAccess OutOfBoundPtr)                     -- impl_mem.ml:1763-1765
        else match alloc.isReadonly with
          | .IsReadOnly kind => fail_ (MerrWriteOnReadOnly kind)           -- impl_mem.ml:1768-1770
          | .IsWritable =>
            if isAtomicMemberAccess enumDefs tagDefs alloc ty addr then
              -- NOTE: OCaml reports LoadAccess here (impl_mem.ml:1772-1774
              -- — looks like an upstream copy-paste; mirrored as-is)
              fail_ (MerrAccess LoadAccess AtomicMemberof)
            else doStore st (some (allocId, alloc)) unionMem addr

/-! ### Pointer comparisons — impl_mem.ml:1830+ -/

def ptrAddr (pv : PointerValue) : Option Int :=
  match pv with | .PV _ (.PVconcrete _ addr) => some addr | _ => none

/-- eq_ptrval — impl_mem.ml:1830-1881, arm-for-arm (arc-10 S4, register
    finding 8 fix: the previous version collapsed the differing-provenance
    `Eff.msum` fork to a deterministic `false` — visible as trace-COUNT
    divergences in exhaustive mode: coverage ptr3-006, csmith seed 930005).
    * (PVnull, PVnull) → true                                (:1832-1833)
    * (PVnull, _) | (_, PVnull) → false                      (:1834-1836)
    * (PVfunction, PVfunction) → symbolEquality              (:1837-1838)
      (the OCaml Eq_Symbol_sym_dict isEqual_method: digest+nat,
      description-INSENSITIVE — NOT the derived BEq)
    * (PVfunction with SD_Id name, PVconcrete addr) and the swapped arm →
      funptrmap lookup at addr, name comparison; absent → false
                                                             (:1839-1847)
    * (PVfunction, _) | (_, PVfunction) → false              (:1848-1850)
    * (PVconcrete addr1, PVconcrete addr2):                  (:1851-1881)
      - the SW_strict_pointer_equality branch (:1852-1853) is NOT ported:
        the differential pipeline never sets switches (file convention,
        cf. loadM / diffPtrval notes)
      - same-provenance: none/none → true, some/some → id equality,
        device/device → true, mixed → false (:1855-1861,1873); the
        (Prov_symbolic, Prov_symbolic) arm (impl_mem.ml:1905-1914 in THIS
        tree, PNVI-ae-udi; PNVI arc S3): `lookup_iota` both; `Single a`,
        `Single b` → `a = b`; otherwise false — reached only through
        `Prov_symbolic` pointers, which nothing mints at the default switch
        set; a symbolic/non-symbolic pair is the mixed → false arm
      - same-provenance true → addr equality                 (:1875-1876)
      - same-provenance false → msum "pointer equality"
        [("using provenance", false); ("ignoring provenance", addr
        equality)] (:1877-1880) — a real ND fork (NDnd), enumerated by
        both sides' exhaustive runners, so the trace-count doubling is
        oracle-matching by construction. -/
def eqPtrval [CerbGlobal.Switches] (_ : CerbLocation.Loc) (pv1 pv2 : PointerValue) : memM Bool :=
  match pv1, pv2 with
  | .PV _ (.PVnull _), .PV _ (.PVnull _) => memReturn true
  | .PV _ (.PVnull _), _ | _, .PV _ (.PVnull _) => memReturn false
  | .PV _ (.PVfunction s1), .PV _ (.PVfunction s2) =>
    memReturn (symbolEquality s1 s2)
  | .PV _ (.PVfunction (Symbol _ _ (SD_Id funname))), .PV _ (.PVconcrete _ addr)
  | .PV _ (.PVconcrete _ addr), .PV _ (.PVfunction (Symbol _ _ (SD_Id funname))) =>
    ND fun st =>
      (NDactive (match st.funptrmap.find? (fun (a, _) => a == addr) with
        | some (_, (_, funname')) => funname == funname'
        | none => false), st)
  | .PV _ (.PVfunction _), _ | _, .PV _ (.PVfunction _) => memReturn false
  | .PV prov1 (.PVconcrete _ addr1), .PV prov2 (.PVconcrete _ addr2) =>
    let sameProv : Bool := match prov1, prov2 with
      | .Prov_none, .Prov_none => true
      | .Prov_some allocId1, .Prov_some allocId2 => allocId1 == allocId2
      | .Prov_device, .Prov_device => true
      | _, _ => false
    -- :1860-1861 SW_strict_pointer_equality → numeric equality only. The switch
    -- set is refused (Z-24), so the OCaml default arm is the only reachable one;
    -- the set case is loud (seam-hygiene H2, the zap_dead_pointers shape)
    -- impl_mem.ml:1916-1923 (THIS tree): `true → addr eq`, `false → msum "pointer equality"`
    let eqResult (same : Bool) : memM Bool :=
      if same then
        memReturn (addr1 == addr2)
      else
        msum "pointer equality"
          [("using provenance", memReturn false),
           ("ignoring provenance", memReturn (addr1 == addr2))]
    if CerbGlobal.has_switch .strict_pointer_equality then
      kill (Other (MerrOther "eqPtrval: SW_strict_pointer_equality is set but the strict-equality arm (impl_mem.ml:1860-1861) is not ported — switches are refused (Z-24)"))
    else match prov1, prov2 with
      | .Prov_symbolic iota1, .Prov_symbolic iota2 =>
        -- impl_mem.ml:1905-1914 (PNVI-ae-udi): `lookup_iota iota1`, then iota2
        ND fun st =>
          let sameIota : Bool := match lookupIota st iota1, lookupIota st iota2 with
            | .Single allocId1, .Single allocId2 => allocId1 == allocId2
            | _, _ => false
          match eqResult sameIota with
          | ND f => f st
      | _, _ => eqResult sameProv

def nePtrval [LemFuel] [CerbGlobal.Switches] (loc : CerbLocation.Loc) (pv1 pv2 : PointerValue) : memM Bool :=
  nd_bind (eqPtrval loc pv1 pv2) (fun b => memReturn (!b))

/-! Relational pointer operators — impl_mem.ml:1886-1955 (arc-14 S1 F1,
    sem:G1: the kill-paths are restored — these previously returned a
    silent `false` for null/function/mixed operands where upstream FAILS).
    The SW_strict_pointer_relationals branches (:1897 etc. in this tree) are
    guarded in the explicit `if has_switch … then <loud kill> else <default>`
    shape (seam-hygiene H2; the set is refused, Z-24); the non-strict path
    compares concrete addresses regardless of provenance. Only lt_ptrval has a dedicated null arm
    upstream (:1898-1900); gt/le/ge fall to their generic MerrWIP arm —
    mirrored arm-for-arm, including the exact error strings. -/

/-- lt_ptrval — impl_mem.ml:1886-1902. -/
def ltPtrval [CerbGlobal.Switches] (loc : CerbLocation.Loc) (pv1 pv2 : PointerValue) : memM Bool :=
  match pv1, pv2 with
  | .PV _ (.PVconcrete _ a1), .PV _ (.PVconcrete _ a2) =>
    -- :1897-1903 SW_strict_pointer_relationals: refused set (Z-24), set case loud (H2)
    if CerbGlobal.has_switch .strict_pointer_relationals then
      kill (Other (MerrOther "ltPtrval: SW_strict_pointer_relationals is set but the strict-relational arm (impl_mem.ml:1897-1903) is not ported — switches are refused (Z-24)"))
    else memReturn (a1 < a2)                                  -- :1896-1897 (non-strict)
  | .PV _ (.PVnull _), _ | _, .PV _ (.PVnull _) =>
    memFail (MerrWIP "lt_ptrval ==> one null pointer") loc    -- :1898-1900
  | _, _ => memFail (MerrWIP "lt_ptrval") loc                 -- :1901-1902

/-- gt_ptrval — impl_mem.ml:1904-1917. -/
def gtPtrval [CerbGlobal.Switches] (loc : CerbLocation.Loc) (pv1 pv2 : PointerValue) : memM Bool :=
  match pv1, pv2 with
  | .PV _ (.PVconcrete _ a1), .PV _ (.PVconcrete _ a2) =>
    -- :1915-1921 SW_strict_pointer_relationals: refused set (Z-24), set case loud (H2)
    if CerbGlobal.has_switch .strict_pointer_relationals then
      kill (Other (MerrOther "gtPtrval: SW_strict_pointer_relationals is set but the strict-relational arm (impl_mem.ml:1915-1921) is not ported — switches are refused (Z-24)"))
    else memReturn (a1 > a2)                                  -- :1914-1915 (non-strict)
  | _, _ => memFail (MerrWIP "gt_ptrval") loc                 -- :1916-1917

/-- le_ptrval — impl_mem.ml:1919-1935. -/
def lePtrval [CerbGlobal.Switches] (loc : CerbLocation.Loc) (pv1 pv2 : PointerValue) : memM Bool :=
  match pv1, pv2 with
  | .PV _ (.PVconcrete _ a1), .PV _ (.PVconcrete _ a2) =>
    -- :1930-1938 SW_strict_pointer_relationals: refused set (Z-24), set case loud (H2)
    if CerbGlobal.has_switch .strict_pointer_relationals then
      kill (Other (MerrOther "lePtrval: SW_strict_pointer_relationals is set but the strict-relational arm (impl_mem.ml:1930-1938) is not ported — switches are refused (Z-24)"))
    else memReturn (a1 ≤ a2)                                  -- :1930-1932 (non-strict)
  | _, _ => memFail (MerrWIP "le_ptrval") loc                 -- :1934-1935

/-- ge_ptrval — impl_mem.ml:1937-1953. -/
def gePtrval [CerbGlobal.Switches] (loc : CerbLocation.Loc) (pv1 pv2 : PointerValue) : memM Bool :=
  match pv1, pv2 with
  | .PV _ (.PVconcrete _ a1), .PV _ (.PVconcrete _ a2) =>
    -- :1947-1955 SW_strict_pointer_relationals: refused set (Z-24), set case loud (H2)
    if CerbGlobal.has_switch .strict_pointer_relationals then
      kill (Other (MerrOther "gePtrval: SW_strict_pointer_relationals is set but the strict-relational arm (impl_mem.ml:1947-1955) is not ported — switches are refused (Z-24)"))
    else memReturn (a1 ≥ a2)                                  -- :1948-1950 (non-strict)
  | _, _ => memFail (MerrWIP "ge_ptrval") loc                 -- :1952-1953

/-- diff_ptrval — permissive mode mirrors impl_mem.ml:2014-2019: subtract
    concrete addresses regardless of provenance, rejecting null/function pointers.
    Without that option, valid only when BOTH pointers carry the SAME Prov_some allocation id
    and both addresses lie within [base, base+size] of that allocation
    (precond, impl_mem.ml:1955-1959); everything else fails MerrPtrdiff
    (→ UB048_disjoint_array_pointers_subtraction via the fail mapping).
    valid_postcond (impl_mem.ml:1961-1967): strip ONE Array layer off
    diff_ty, then TRUNCATING Z.div of the address difference by
    sizeof(elem). `precond`/`valid_postcond`/`error_postcond` are local
    functions as upstream's are (:1999-2013 in THIS tree).
    PNVI-ae-udi arms (PNVI arc S3; impl_mem.ml:2031-2105 in THIS tree, reached
    only through `Prov_symbolic` pointers, which nothing mints at the default
    switch set): (symbolic, Prov_some) and (Prov_some, symbolic) :2032-2060 —
    `Single a` → `a = id'` and precond on `a`'s allocation; `Double (a, b)` →
    `id' ∈ {a, b}` and precond on `id'`'s allocation, which collapses the iota to
    `Single id'`; (symbolic, symbolic) :2063-2105 — the intersection of the two
    entries: none → error; `Single i` → both iotas collapse to `i`, valid (NO
    precond, as upstream); `Double` → `addr1 = addr2` gives zero, otherwise
    upstream's `fail (MerrOther "in `diff_ptrval` invariant of PNVI-ae-udi
    failed: …")` (:2104) — its own invariant failure, not a verdict about the
    program — is REFUSED (design §G.1 row R12, class (A′), `R-PNVI-08`). -/
def diffPtrval [LemFuel] [CerbGlobal.Switches] (enumDefs : EnumDefs) (tagDefs : TagDefs) (loc : CerbLocation.Loc) (diffTy : ctype) (pv1 pv2 : PointerValue) : memM IntegerValue :=
  ND fun st =>
    let precond (alloc : Allocation) (addr1 addr2 : Int) : Bool :=  -- impl_mem.ml:1955-1959
      alloc.base ≤ addr1 && addr1 ≤ alloc.base + alloc.size &&
      alloc.base ≤ addr2 && addr2 ≤ alloc.base + alloc.size
    let validPostcond (addr1 addr2 : Int) (st' : MemState) :=
      let diffTy' := match diffTy with  -- impl_mem.ml:1962-1966
        | Ctype _ (.Array0 elemTy _) => elemTy
        | _ => diffTy
      (NDactive (integerIval
        (integerDiv_t (addr1 - addr2) (sizeofCtype enumDefs tagDefs diffTy' : Int))), st')
    let errorPostcond := (NDkilled (failReason MerrPtrdiff loc), st)
    -- get_allocation ~loc — impl_mem.ml:669-675
    let getAllocFail (allocId : StorageInstanceId) :=
      (NDkilled (failReason (MerrOutsideLifetime
        s!"Concrete.get_allocation, alloc_id={allocId}") loc), st)
    -- impl_mem.ml:2014-2019: permissive subtraction accepts concrete addresses
    -- independently of provenance; null/function pointers still fail.
    if CerbGlobal.has_switch (.pointer_arith .PERMISSIVE) then
      match pv1, pv2 with
      | .PV _ (.PVconcrete _ addr1), .PV _ (.PVconcrete _ addr2) =>
        validPostcond addr1 addr2 st
      | _, _ => errorPostcond
    else match pv1, pv2 with
    | .PV (.Prov_some allocId1) (.PVconcrete _ addr1),
      .PV (.Prov_some allocId2) (.PVconcrete _ addr2) =>
      if allocId1 == allocId2 then
        match st.allocations.get? allocId1 with
        | none => getAllocFail allocId1
        | some alloc =>
          if precond alloc addr1 addr2 then validPostcond addr1 addr2 st
          else errorPostcond
      else errorPostcond
    | .PV (.Prov_symbolic iota) (.PVconcrete _ addr1), .PV (.Prov_some allocId') (.PVconcrete _ addr2)
    | .PV (.Prov_some allocId') (.PVconcrete _ addr1), .PV (.Prov_symbolic iota) (.PVconcrete _ addr2) =>
      -- impl_mem.ml:2032-2060 (PNVI-ae-udi)
      match lookupIota st iota with
      | .Single allocId =>
        if allocId == allocId' then
          match st.allocations.get? allocId with
          | none => getAllocFail allocId
          | some alloc =>
            if precond alloc addr1 addr2 then validPostcond addr1 addr2 st
            else errorPostcond
        else errorPostcond
      | .Double allocId1 allocId2 =>
        if allocId1 == allocId' || allocId2 == allocId' then
          match st.allocations.get? allocId' with
          | none => getAllocFail allocId'
          | some alloc =>
            if precond alloc addr1 addr2 then
              validPostcond addr1 addr2 { st with iotaMap := st.iotaMap.insert iota (.Single allocId') }
            else errorPostcond
        else errorPostcond
    | .PV (.Prov_symbolic iota1) (.PVconcrete _ addr1), .PV (.Prov_symbolic iota2) (.PVconcrete _ addr2) =>
      -- impl_mem.ml:2063-2105 (PNVI-ae-udi): `lookup_iota iota1`, then iota2; the
      -- intersection :2068-2088
      let interIds : Option IotaEntry :=
        match lookupIota st iota1, lookupIota st iota2 with
        | .Single x, .Single y => if x == y then some (.Single x) else none
        | .Single x, .Double y z | .Double y z, .Single x =>
          if x == y || x == z then some (.Single x) else none
        | .Double x1 x2, .Double y1 y2 =>
          if x1 == y1 then
            if x2 == y2 then some (.Double x1 x2) else some (.Single x1)
          else if x2 == y2 then some (.Single x2)
          else none
      match interIds with
      | none => errorPostcond
      | some (.Single allocId') =>
        -- :2093-2097 `IntMap.add iota1 (Single i) (IntMap.add iota2 (Single i) map)`
        validPostcond addr1 addr2
          { st with iotaMap := (st.iotaMap.insert iota2 (.Single allocId')).insert iota1 (.Single allocId') }
      | some (.Double _ _) =>
        if addr1 == addr2 then validPostcond addr1 addr2 st  -- :2100-2101 (zero)
        else
          -- ascribed at memM (pnviRefuseM): the leaf's kernel default is a kill, not an active pair
          match (pnviRefuseM "R-PNVI-08: diff_ptrval, (Prov_symbolic, Prov_symbolic), ambiguous intersection with addr1 <> addr2 — impl_mem.ml:2104 `fail ~loc (MerrOther \"in `diff_ptrval` invariant of PNVI-ae-udi failed: ambiguous iotas with addr1 <> addr2\")` (upstream's own invariant failure)" : memM IntegerValue) with
          | ND f => f st
    | _, _ => errorPostcond

/-! ### Pointer validity -/

/-- Strip Atomic wrapper — mirrors OCaml unatomic_. -/
private def unatomic_ : ctype → ctype_
  | Ctype _ (.Atomic inner) => match inner with | Ctype _ t => t
  | Ctype _ t => t

/-- isWellAligned_ptrval — impl_mem.ml:2065-2083, arm for arm.
    `unatomic_ ref_ty` = `Void | Function _` → ONE MerrOther message
    (:2067-2069; zero-discrepancy Z-21/Z2-M-09: this had two messages and
    put `FunctionNoParams` in the arm — the OCaml `Function _` does NOT
    match `FunctionNoParams`, which falls to the `_` arm: a null pointer
    answers `true`, a concrete one reaches `alignof ref_ty` = `assert
    false` (:216-218) — here alignofCtype's function-type panic — and no
    accepted C shape reaches it, tests/z2-probes/mem/funptr_noparams_*).
    Null → true (:2072-2073); function pointer → MerrOther (:2074-2075);
    concrete → `modulus addr (alignof ref_ty) = 0` (:2080) — no `.max 1`
    (Z2-M-10: alignof ≥ 1 for every type that reaches this arm). -/
def isWellAlignedPtrval [LemFuel] (enumDefs : EnumDefs) (tagDefs : TagDefs) (ty : ctype) (pv : PointerValue) : memM Bool :=
  match unatomic_ ty with
  | .Void0 | .Function _ _ _ =>
    memFail (MerrOther "called isWellAligned_ptrval on void or a function type")
  | _ =>
    match pv with
    | .PV _ (.PVnull _) => memReturn true
    | .PV _ (.PVfunction _) =>
      memFail (MerrOther "called isWellAligned_ptrval on function pointer")
    | .PV _ (.PVconcrete _ addr) =>
      memReturn (addr % (alignofCtype enumDefs tagDefs ty : Int) == 0)

/-- validForDeref_ptrval — impl_mem.ml:2086-2123 (§6.5.3.3 footnote 102).
    Null/function pointer → false.
    Prov_none → false.
    Prov_device → checks alignment.
    Prov_some → checks !is_dead && well-aligned (`do_test`, :2136-2141 in THIS tree).
    Prov_symbolic (PNVI-ae-udi; impl_mem.ml:2152-2163, PNVI arc S3) →
    `lookup_iota`: `Single a` → `do_test a`; `Double (a, b)` → `do_test a`,
    and if false `do_test b`. Reached only through a `Prov_symbolic` pointer,
    which nothing mints at the default switch set. -/
def validForDerefPtrval [LemFuel] (enumDefs : EnumDefs) (tagDefs : TagDefs) (ty : ctype) (pv : PointerValue) : memM Bool :=
  ND fun st =>
    match pv with
    | .PV _ (.PVnull _) | .PV _ (.PVfunction _) =>
      (NDactive false, st)
    | .PV .Prov_none _ =>
      (NDactive false, st)
    | .PV .Prov_device _ =>
      -- Device pointer: only check alignment (no liveness tracking)
      match isWellAlignedPtrval enumDefs tagDefs ty pv with
      | ND f => f st
    | .PV (.Prov_some allocId) _ =>
      if st.deadAllocations.contains allocId then
        (NDactive false, st)
      else
        match isWellAlignedPtrval enumDefs tagDefs ty pv with
        | ND f => f st
    | .PV (.Prov_symbolic iota) (.PVconcrete _ _) =>
      -- impl_mem.ml:2152-2163 (PNVI-ae-udi)
      let doTest (z : StorageInstanceId) : memM Bool :=     -- :2136-2141
        ND fun s =>
          if s.deadAllocations.contains z then (NDactive false, s)
          else match isWellAlignedPtrval enumDefs tagDefs ty pv with
            | ND f => f s
      let test : memM Bool :=
        match lookupIota st iota with
        | .Single allocId => doTest allocId
        | .Double allocId1 allocId2 =>
          nd_bind (doTest allocId1) fun ok =>
            if ok then memReturn true else doTest allocId2
      match test with
      | ND f => f st

/-! ### Pointer casts -/

/-- wrapI: wrap `n` into range [min, max] per C's unsigned conversion. -/
private def wrapI (n : Int) (lo hi : Int) : Int :=
  let dlt := hi - lo + 1
  let r := n % dlt
  let r := if r < 0 then r + dlt else r
  if r <= hi then r else r - dlt

/-- ptrfromint — impl_mem.ml:2126-2173. wrapI into the pointer range
    (:2132-2145), then the PVI arm structure (:2163-2173) — zero-discrepancy
    Z-06 (noodle D5): a provenance-less integer inside `deviceRanges` becomes
    a `Prov_device` pointer (:2165-2167); NULL only for a provenance-less
    zero (:2168-2169; an integer CARRYING a provenance keeps it and yields a
    concrete pointer even at 0, :2172-2173 — the charter's Z-09). The
    is_PNVI arm (impl_mem.ml:2190-2205 in THIS tree; PNVI arc S3): `n = 0` →
    `PVnull`; else `find_overlaping st n` — `NoAlloc` → `Prov_none`,
    `SingleAlloc id` → `Prov_some id`, `DoubleAlloc ids` → a fresh iota
    (`add_iota`) → `Prov_symbolic iota` — and `PV (prov, PVconcrete (None, n))`.
    The integer's own provenance is ignored and NO device range is consulted
    under PNVI: upstream's `(* TODO: device memory? *)` (:2191) is MIRRORED, not
    resolved (design §G.1 row R7, §F.15, accepted [USER 2026-10-05] in §H). At
    the default switch set `is_PNVI () = false` by `rfl`: the PVI arm. -/
def ptrfromint [CerbGlobal.Switches] (_ : CerbLocation.Loc) (_ : integerType) (refTy : ctype)
    (iv : IntegerValue) : memM PointerValue :=
  match iv with
  | .IV prov nRaw =>
    -- :2132-2145 wrapI to [0, 2^(8*sizeof_pointer) - 1]
    let hi : Int := (2 : Int) ^ (targetPtrSize * 8) - 1
    let n := wrapI nRaw 0 hi
    if CerbGlobal.is_PNVI () then
      -- impl_mem.ml:2190-2205; `(* TODO: device memory? *)` (:2191) mirrored
      if n == 0 then memReturn (.PV .Prov_none (.PVnull refTy))               -- :2192-2193
      else ND fun st =>
        match findOverlapping st n with                                         -- :2196
        | .NoAlloc => (NDactive (.PV .Prov_none (.PVconcrete none n)), st)       -- :2197-2198
        | .SingleAlloc allocId =>
          (NDactive (.PV (.Prov_some allocId) (.PVconcrete none n)), st)        -- :2199-2200
        | .DoubleAlloc allocId1 allocId2 =>                                      -- :2201-2203
          let (iota, st') := addIota (allocId1, allocId2) st
          (NDactive (.PV (.Prov_symbolic iota) (.PVconcrete none n)), st')
    else match prov with
    | .Prov_none =>
      if deviceRanges.any (fun (lo, hi) => lo ≤ n && n ≤ hi) then
        memReturn (.PV .Prov_device (.PVconcrete none n))                 -- :2165-2167
      else if n == 0 then memReturn (.PV .Prov_none (.PVnull refTy))     -- :2168-2169
      else memReturn (.PV .Prov_none (.PVconcrete none n))              -- :2170-2171
    | _ => memReturn (.PV prov (.PVconcrete none n))                     -- :2172-2173

/-- intfromptr — impl_mem.ml:2439-2461 (older numbering; :2483-2505 in THIS tree).
    For concrete pointer: validate address fits in target integer type,
    fail with MerrIntFromPtr on overflow. Every result goes through `mk_ival`
    (:2486, :2488, :2505 — `IV (Prov_none, n)` under any PNVI variant, `IV
    (prov, n)` otherwise). PNVI arc S3: the `has_switch (SW_PNVI AE) ||
    has_switch (SW_PNVI AE_UDI)` arm (:2490-2498) exposes the pointer's
    allocation (`expose_allocation`, a `Prov_some` only) BEFORE the range check;
    the exact upstream test (so `PNVI PLAIN` takes the no-exposure arm). At the
    default switch set both tests are `false` by `rfl`: `mkIval prov n = IV prov n`
    and no exposure. -/
def intfromptr [CerbGlobal.Switches] (enumDefs : EnumDefs) (tagDefs : TagDefs) (loc : CerbLocation.Loc) (_ : ctype) (ity : integerType)
    (pv : PointerValue) : memM IntegerValue :=
  match pv with
  | .PV prov (.PVnull _) => memReturn (mkIval prov 0)                        -- :2485-2486
  -- named-deviation register N1 (VALIDATION.md §2b): `n` is the symbol's
  -- fresh-supply number, which the oracle numbers differently. Served, not
  -- refused: libc's atexit round-trips a function pointer through uintptr_t
  -- (runtime/libc/src/stdlib.c:194-199) and must keep working.
  | .PV prov (.PVfunction (Symbol _ n _)) => memReturn (mkIval prov n)      -- :2487-2488
  | .PV prov (.PVconcrete _ addr) =>
    let rangeChecked : memM IntegerValue :=
      let (.IV _ ityMin) := minIval enumDefs tagDefs ity
      let (.IV _ ityMax) := maxIval enumDefs tagDefs ity
      if addr < ityMin || ityMax < addr then
        -- impl_mem.ml:2459 `fail ~loc MerrIntFromPtr` — the C cast site; the
        -- loc was dropped here (memFail's `other "Concrete"` default), so UB024
        -- printed `other_location(Concrete)` (zero-discrepancy Z-02, noodle D2)
        memFail MerrIntFromPtr loc
      else
        memReturn (mkIval prov addr)                                         -- :2505
    -- :2490-2498 (THIS tree) `if has_switch (SW_PNVI AE) || has_switch (SW_PNVI
    -- AE_UDI) then (match prov with Prov_some id -> expose_allocation id | _ ->
    -- return ()) else return ()`, before the range check (PNVI arc S3)
    if CerbGlobal.has_switch (.PNVI .AE) || CerbGlobal.has_switch (.PNVI .AE_UDI) then
      match prov with
      | .Prov_some allocId =>
        ND fun st =>
          match rangeChecked with
          | ND f => f (exposeAllocation allocId st)
      | _ => rangeChecked
    else rangeChecked

/-! ### Effectful pointer shifts -/

/-- eff_array_shift_ptrval — impl_mem.ml:2244-2356 (older numbering; :2288-2400
    in THIS tree) (zero-discrepancy Z-17: this used to delegate to the PURE
    `array_shift_ptrval`, whose null arm panics where this one fails UB046, whose
    GNU void-byte arm this one lacks — `sizeof void` is `assert false`, :134-135,
    so a void element type panics in sizeofCtype here as it does there — and
    which keeps the union-member tag this one DROPS).
    `offset = sizeof ty * ival` (:2246); null → `fail ~loc MerrArrayShift`
    = UB046 (:2247-2251; upstream's commented-out TODO-failwith is NOT live — the
    live arm is mirrored, design §G.1 R14 / §H); PVfunction → `failwith`
    (:2252-2253, fail-stop, Q4 — UNCHANGED by PNVI arc S3: this function is on
    the DEFAULT path, `runtime/libcore/std.core:188/196/212/217` emit
    `PtrArrayShift` in default mode, so design §G.1 row R13's "not on the default
    path" premise does not hold; the site is left as it was and reported, S3
    record); `Prov_some` (:2325-2337) → `PV (Prov_some id, PVconcrete (None,
    addr + offset))`; `Prov_none` (:2338-2343) → likewise with `Prov_none`;
    `Prov_device` (:2344-2346) → likewise.
    The bounds arms are selected by `SW_pointer_arith STRICT || (is_PNVI () &&
    not PERMISSIVE)` (:2309-2310 / :2381-2382 / :2393-2394 in THIS tree):
    * the `STRICT` disjunct is a refused switch whose arms are not ported — the
      explicit loud kill (seam-hygiene H2);
    * the `is_PNVI ∧ ¬PERMISSIVE` disjunct is LIVE (PNVI arc S3): `Prov_some` →
      `get_allocation ~loc` then `base ≤ shifted ∧ shifted + sizeof ty ≤ base +
      size + sizeof ty` (one past allowed) else `fail ~loc MerrArrayShift`
      (:2378-2390; upstream's `(* TODO: is it correct to use the "ty" as the
      lvalue_ty? *)` MIRRORED, design §G.1 row R15, §H); `Prov_none` → `fail ~loc
      (MerrOther "out-of-bound pointer arithmetic (Prov_none)")` (:2391-2395);
      `Prov_device` → no guard (:2396-2400, `(* TODO: check *)` MIRRORED, R17).
    * `Prov_symbolic` (:2301-2376, PNVI-ae-udi; reached only through a
      `Prov_symbolic` pointer, never minted at the default set): `precond z` =
      the same bounds check on `z`'s allocation under `is_PNVI ∧ ¬PERMISSIVE`,
      else `true`; `Double (a, b)` with `ival ≠ 0`: precond a ∧ precond b →
      PERMISSIVE ? no collapse : upstream's `Printf.printf "id1= …"` to STDOUT
      then `fail (MerrOther "(PNVI-ae-uid) ambiguous non-zero array shift")`
      (:2326-2334) — a debug print in a semantics arm, REFUSED (design §G.1 row
      R16, class (B), `R-PNVI-10`; nothing is written to stdout); precond a only
      → collapse to a; precond b only → collapse to b; neither → MerrArrayShift;
      `ival = 0`: precond a ∨ precond b, else MerrArrayShift; `Single a`: precond
      a, else MerrArrayShift; the result keeps `Prov_symbolic iota`.
    At the default switch set `is_PNVI () = false` and `STRICT` is unset (`rfl`):
    the guard is `false` and every concrete arm is the plain shift, as before S3.
    Evaluation-order note: the OCaml computes `offset` (hence `sizeof ty`) BEFORE
    matching the pointer, so a void element type asserts even for a null pointer;
    here `offset` is computed in the concrete arms only (a null pointer with a
    void element type fails UB046 instead of asserting — a corner recorded since
    Z-17). -/
def effArrayShiftPtrval [LemFuel] [CerbGlobal.Switches] (enumDefs : EnumDefs) (tagDefs : TagDefs) (loc : CerbLocation.Loc) (pv : PointerValue) (elemTy : ctype) (iv : IntegerValue) : memM PointerValue :=
  match pv, iv with
  | .PV _ (.PVnull _), _ => memFail MerrArrayShift loc                             -- :2247-2251
  | .PV _ (.PVfunction _), _ => failStopMem "Concrete.eff_array_shift_ptrval, PVfunction"  -- :2252-2253
  | .PV (.Prov_symbolic iota) (.PVconcrete _ addr), .IV _ ival =>
    -- impl_mem.ml:2301-2376 (THIS tree), PNVI-ae-udi
    let sz : Int := (sizeofCtype enumDefs tagDefs elemTy : Int)
    let shiftedAddr := addr + sz * ival                                            -- :2306
    if CerbGlobal.has_switch (.pointer_arith .STRICT) then
      kill (Other (MerrOther "effArrayShiftPtrval: SW_pointer_arith STRICT is set but the strict bounds-checking arms (impl_mem.ml:2309-2310, 2381-2382, 2393-2394) are not ported — switches are refused (Z-24)"))
    else ND fun st =>
      -- precond z — :2307-2319 (the STRICT disjunct is the loud kill above)
      let precond (z : StorageInstanceId) : Except (kill_reason mem_error) Bool :=
        if CerbGlobal.is_PNVI () && !CerbGlobal.has_switch (.pointer_arith .PERMISSIVE) then
          match getAllocationE loc st z with
          | .error k => .error k
          | .ok alloc => .ok (alloc.base ≤ shiftedAddr && shiftedAddr + sz ≤ alloc.base + alloc.size + sz)
        else .ok true
      let result (st' : MemState) := (NDactive (.PV (.Prov_symbolic iota) (.PVconcrete none shiftedAddr)), st')
      let collapse (allocId : StorageInstanceId) :=
        result { st with iotaMap := st.iotaMap.insert iota (.Single allocId) }     -- :2347-2350
      let arrayShiftFail := (NDkilled (failReason MerrArrayShift loc), st)
      match lookupIota st iota with                                                 -- :2320
      | .Double allocId1 allocId2 =>
        if ival != 0 then                                                           -- :2322-2353
          match precond allocId1 with
          | .error k => (NDkilled k, st)
          | .ok true =>
            match precond allocId2 with
            | .error k => (NDkilled k, st)
            | .ok true =>
              if CerbGlobal.has_switch (.pointer_arith .PERMISSIVE) then result st   -- :2328-2329 `NoCollapse
              else
                -- ascribed at memM (pnviRefuseM): the leaf's kernel default is a kill, not an active pair
                match (pnviRefuseM s!"R-PNVI-10: eff_array_shift_ptrval, Prov_symbolic, Double, non-zero shift admitted by both allocations ({allocId1}, {allocId2}) — impl_mem.ml:2331-2334 `Printf.printf \"id1= %s, id2= %s ==> addr= %s\\n\" …; fail ~loc (MerrOther \"(PNVI-ae-uid) ambiguous non-zero array shift\")` (a debug print to stdout in a semantics arm)" : memM PointerValue) with
                | ND f => f st
            | .ok false => collapse allocId1                                         -- :2336-2337
          | .ok false =>
            match precond allocId2 with
            | .error k => (NDkilled k, st)
            | .ok true => collapse allocId2                                          -- :2341-2342
            | .ok false => arrayShiftFail                                            -- :2343-2344
        else                                                                        -- :2354-2366
          match precond allocId1 with
          | .error k => (NDkilled k, st)
          | .ok true => result st
          | .ok false =>
            match precond allocId2 with
            | .error k => (NDkilled k, st)
            | .ok true => result st
            | .ok false => arrayShiftFail
      | .Single allocId =>                                                          -- :2367-2373
        match precond allocId with
        | .error k => (NDkilled k, st)
        | .ok true => result st
        | .ok false => arrayShiftFail
  | .PV prov (.PVconcrete _ addr), .IV _ ival =>
    let offset : Int := (sizeofCtype enumDefs tagDefs elemTy : Int) * ival               -- :2246
    -- :2381-2382 (Prov_some) / :2393-2394 (Prov_none) in THIS tree: `SW_pointer_arith
    -- STRICT || (is_PNVI () && not PERMISSIVE)` selects the bounds-checking arms; the
    -- Prov_device arm (:2396-2400) has no guard. `false` at the default set (`rfl`).
    if (match prov with | .Prov_device => false | _ => true) &&
       (CerbGlobal.has_switch (.pointer_arith .STRICT) ||
        (CerbGlobal.is_PNVI () && !CerbGlobal.has_switch (.pointer_arith .PERMISSIVE))) then
      -- the STRICT disjunct: refused set (Z-24), its arms are not ported — loud
      -- (seam-hygiene H2); the `is_PNVI ∧ ¬PERMISSIVE` disjunct: the live arms
      if CerbGlobal.has_switch (.pointer_arith .STRICT) then
        kill (Other (MerrOther "effArrayShiftPtrval: SW_pointer_arith STRICT is set but the strict bounds-checking arms (impl_mem.ml:2309-2310, 2381-2382, 2393-2394) are not ported — switches are refused (Z-24)"))
      else
        let shiftedAddr := addr + offset
        match prov with
        | .Prov_some allocId =>
          -- :2378-2390 (THIS tree); `(* TODO: is it correct to use the "ty" as the
          -- lvalue_ty? *)` (:2379) mirrored (design §G.1 R15, §H)
          ND fun st =>
            match getAllocationE loc st allocId with
            | .error k => (NDkilled k, st)
            | .ok alloc =>
              let sz : Int := (sizeofCtype enumDefs tagDefs elemTy : Int)
              if alloc.base ≤ shiftedAddr && shiftedAddr + sz ≤ alloc.base + alloc.size + sz then
                (NDactive (.PV (.Prov_some allocId) (.PVconcrete none shiftedAddr)), st)
              else (NDkilled (failReason MerrArrayShift loc), st)
        | .Prov_none =>
          memFail (MerrOther "out-of-bound pointer arithmetic (Prov_none)") loc        -- :2391-2395
        | .Prov_device =>
          -- unreachable: excluded by the guard above; :2396-2400's arm verbatim
          memReturn (.PV .Prov_device (.PVconcrete none shiftedAddr))
        | .Prov_symbolic _ =>
          -- unreachable: matched by the Prov_symbolic arm above; loud, never absorbed
          failStopMem "effArrayShiftPtrval: a Prov_symbolic pointer reached the Prov_some/Prov_none bounds arms (unreachable: the Prov_symbolic arm matches first)"
    else memReturn (.PV prov (.PVconcrete none (addr + offset)))                -- :2336/:2343/:2346

def effMemberShiftPtrval [LemFuel] (enumDefs : EnumDefs) (tagDefs : TagDefs) (_ : CerbLocation.Loc) (pv : PointerValue) (tag : sym) (member : identifier) : memM PointerValue :=
  memReturn (memberShiftPtrval enumDefs tagDefs pv tag member)

/-! ### Memory operations -/

/-- memcpy — impl_mem.ml:2635-2646 (arc-14 S1 F1, sem:G2: previously
    copied raw bytemap bytes, silently bypassing every access check).
    Mirrored as upstream writes it: a per-byte loop of CHECKED
    `load`/`store` of `unsigned char` at `array_shift_ptrval` offsets, so
    OOB source/destination, dead or read-only destination, and atomicity
    violations kill exactly as the oracle's load/store machinery does.
    Upstream's own TODOs (overlap-UB unimplemented) inherit unchanged.
    The loop recurses on a Nat countdown (structural; upstream counts up
    with `Z.lt i size_n`, same iteration space). -/
def memcpyM [LemFuel] [CerbGlobal.Switches] (enumDefs : EnumDefs) (tagDefs : TagDefs) (loc : CerbLocation.Loc) (dst src : PointerValue) (sizeIv : IntegerValue) : memM PointerValue :=
  match sizeIv with
  | .IV _ size_n =>
    let rec aux : Nat → Int → memM PointerValue
      | 0, _ => memReturn dst                                        -- :2643-2644
      | k + 1, i =>
        -- :2640-2642: load uchar (src+i) >>= store uchar (dst+i)
        nd_bind (loadM enumDefs tagDefs loc unsigned_char
            (arrayShiftPtrval enumDefs tagDefs src unsigned_char (.IV .Prov_none i))) fun lr =>
        nd_bind (storeM enumDefs tagDefs loc unsigned_char false
            (arrayShiftPtrval enumDefs tagDefs dst unsigned_char (.IV .Prov_none i)) lr.2) fun _ =>
        aux k (i + 1)
    aux size_n.toNat 0

/-- memcmp — impl_mem.ml:2649-2665 (arc-14 S1 F1, sem:G2: previously read
    raw bytemap bytes with unspecified bytes silently comparing equal).
    Mirrored: per-byte CHECKED `load` of `unsigned char` on both sides;
    a load that does not produce `MVinteger` — an unspecified
    (uninitialised) byte — hits upstream's own `assert false`
    (impl_mem.ml:2658-2659), mirrored here as a loud panic (fail-stop
    under LEAN_ABORT_ON_PANIC; both sides crash rather than invent a
    value — the oracle's inelegant-but-fail-closed behavior, mirrored
    not improved; see tests/immaculate g2-memcmp-uninit).
    Byte comparison is on the loaded integer VALUES (Z.compare upstream,
    :2662-2664), fold stopping at the first nonzero.
    DECLARED (zero-discrepancy Z2-M-13): the size argument goes through
    `Int.toNat`, which maps a negative size_n to 0 (empty comparison,
    result 0) — upstream `Z.to_int size_n` (:2660) keeps the negative and
    get_bytes' `| size` arm (:2652-2659) then recurses on size-1 forever
    (non-termination, no verdict). Reachability: memcmp's `size_t` is
    non-negative after conv_int, so no C program reaches a negative size;
    a non-terminating mirror would be a FUEL kill (EXC(b)) here — the
    total rendering is kept and declared. (memcpy, :2637-2644 `Z.lt i
    size_n`, runs ZERO iterations on a negative size on both sides — no
    difference there.) -/
def memcmpM [LemFuel] [CerbGlobal.Switches] (enumDefs : EnumDefs) (tagDefs : TagDefs) (pv1 pv2 : PointerValue) (sizeIv : IntegerValue) : memM IntegerValue :=
  match sizeIv with
  | .IV _ size_n =>
    -- get_bytes — impl_mem.ml:2650-2659 (ptr' = ptr+1 uchar per step)
    let rec getBytes (ptrval : PointerValue) (acc : List Int) : Nat → memM (List Int)
      | 0 => memReturn acc.reverse
      | k + 1 =>
        nd_bind (loadM enumDefs tagDefs CerbLocation.unknown unsigned_char ptrval) fun lr =>
        match lr.2 with
        | .MVinteger _ (.IV _ byte_n) =>
          let ptr' := arrayShiftPtrval enumDefs tagDefs ptrval unsigned_char (.IV .Prov_none 1)
          getBytes ptr' (byte_n :: acc) k
        | _ =>
          -- impl_mem.ml:2658-2659: assert false (unspecified byte)
          failStopMem "Concrete.memcmp: non-integer byte (impl_mem.ml:2658-2659 assert false)"
    -- ISO-fix register R3 (VALIDATION.md §2, ADMITTED BY CLASS — [USER 2026-09-03]
    -- referent ruling, confirmed [USER 2026-09-05] "(2) agree"): upstream converts the
    -- size with `Z.to_int size_n` (impl_mem.ml:2660-2661), which raises Z.Overflow for a
    -- size outside OCaml's native int range BEFORE any byte is read; here the size feeds
    -- the checked per-byte loads directly, so a huge size reaches the semantics' own
    -- out-of-bound UB (pin tests/immaculate/libc/s4b-memcmp-hugesize: ORACLE_CRASH /
    -- L=UB_CERB002a; tray 13).
    nd_bind (getBytes pv1 [] size_n.toNat) fun bytes1 =>
    nd_bind (getBytes pv2 [] size_n.toNat) fun bytes2 =>
    -- impl_mem.ml:2661-2664
    memReturn (integerIval ((bytes1.zip bytes2).foldl (init := (0 : Int))
      fun acc (n1, n2) =>
        if acc == 0 then (if n1 < n2 then -1 else if n1 > n2 then 1 else 0)
        else acc))

/-- realloc — impl_mem.ml:2668-2696.
    null → allocate_region (fresh)
    concrete + dynamic + live + base → allocate new, memcpy, kill old
    everything else → MerrWIP failure -/
def reallocM [LemFuel] [CerbGlobal.Switches] (enumDefs : EnumDefs) (tagDefs : TagDefs) (loc : CerbLocation.Loc) (tid : Nat) (align : IntegerValue)
    (ptr : PointerValue) (size : IntegerValue) : memM PointerValue :=
  match ptr with
  | .PV .Prov_none (.PVnull _) =>
    allocateRegion tid (PrefOther "realloc") align size          -- :2670-2671
  | .PV .Prov_none _ =>
    memFail (MerrWIP "realloc no provenance") loc                -- :2672-2673
  | .PV (.Prov_some allocId) (.PVconcrete _ addr) =>
    ND fun st =>
      let isDynamic := st.dynamicAddrs.contains addr             -- is_dynamic, :2675
      let isDead := st.deadAllocations.contains allocId          -- is_dead, :2678
      -- fail mapping (impl_mem.ml:540-546): MerrUndefinedRealloc →
      -- UB179c/d (Mem_common undefinedFromMem_error). Arc-14 S1 F1,
      -- sem:G3: these previously raised MerrUndefinedFree (UB179a/b) —
      -- the wrong UB family, and the old comment even miscited it.
      if !isDynamic then
        (NDkilled (failReason (MerrUndefinedRealloc Free_non_matching) loc), st)    -- :2676-2677
      else if isDead then
        (NDkilled (failReason (MerrUndefinedRealloc Free_dead_allocation) loc), st) -- :2679-2681
      else match st.allocations.get? allocId with
        | none =>
          -- get_allocation ~loc:(other "Concrete.realloc") — :2683 (fails
          -- MerrOutsideLifetime via get_allocation, impl_mem.ml:669-675,
          -- with THAT loc — zero-discrepancy Z-20: the default loc was
          -- passed here; unreachable — a dynamic, non-dead address always
          -- has its allocation — mirrored anyway)
          (NDkilled (failReason
            (MerrOutsideLifetime s!"Concrete.get_allocation, alloc_id={allocId}")
            (CerbLocation.other "Concrete.realloc")), st)
        | some alloc =>
          if alloc.base == addr then
            -- impl_mem.ml:2685-2691: allocate_region >>= memcpy (the
            -- CHECKED per-byte copy — see memcpyM) >>= kill >>= return.
            -- size_to_copy = IV (Prov_none, min alloc.size size_n), :2686-2688.
            let sizeToCopy : IntegerValue := match size with
              | .IV _ size_n => .IV .Prov_none (min alloc.size size_n)
            let chain : memM PointerValue :=
              nd_bind (allocateRegion tid (PrefOther "realloc") align size) fun newPtr =>
              nd_bind (memcpyM enumDefs tagDefs loc newPtr ptr sizeToCopy) fun _ =>
              nd_bind (killM (CerbLocation.other "realloc") true ptr) fun _ =>
              memReturn newPtr
            (match chain with | ND f => f st)
          else
            (NDkilled (failReason (MerrWIP "realloc: invalid pointer") loc), st)    -- :2692-2693
  | _ => memFail (MerrWIP "realloc: invalid pointer") loc        -- :2695-2696

/-! ### Prefix operations -/

/-- update_prefix — impl_mem.ml:1349-1362 (arc-14 S1 F1, sem:S5: was a
    silent no-op; the prefix is semantically LIVE — storeM's is_locking
    arm selects the readonly KIND from `alloc.prefix_`, see :1573-1577's
    mirror above). MVpointer with Prov_some → update that allocation's
    prefix; a missing allocation or non-pointer argument warns upstream
    (Cerb_debug.warn, no debug facility on the batch path here) and
    returns unit — same observable behavior. -/
def updatePrefix : prefix0 × MemValue → memM Unit
  | (pref, .MVpointer _ (.PV (.Prov_some allocId) _)) =>
    ND fun st =>
      match st.allocations.get? allocId with
      | some alloc =>                                            -- :1353-1355
        (NDactive (), { st with
          allocations := st.allocations.insert allocId { alloc with prefix_ := pref } })
      | none => (NDactive (), st)                                -- :1356-1358 (warn)
  | _ => memReturn ()                                            -- :1360-1362 (warn)
/-- prefix_of_pointer — impl_mem.ml:1364-1418 computes `Some (string_of_prefix
    alloc.prefix ^ …)` (base / `.member` / `[index]` forms) for a Prov_some
    pointer, `None` otherwise.
    DECLARED (zero-discrepancy Z2-M-06): NOT ported — returns `none`.
    Reachability argument: the only callers are driver.lem:689, :702 and
    :714, which store the result in `dr_st.trace` (`ME_load`/`ME_store`/
    `ME_seq_rmw` entries) consumed only by `--trace` and the web UI — never
    by the batch verdict line, the exit code, stdout or stderr. Port (S-M)
    when `--trace` parity is wanted. -/
def prefixOfPointer (_ : PointerValue) : memM (Option String) := memReturn none

/-! ### Varargs

Mirrors impl_mem.ml:2698-2764 (va_start/va_copy/va_arg/va_end/va_list) on
the assoc-list `varargs` / `nextVarargsId` MemState fields (the faithful
mirror of OCaml's `varargs: (int * (ctype * pointer_value) list) IntMap.t`
+ `next_varargs_id`, impl_mem.ml:490-491).

PROTOTYPE PROVENANCE: the case structure follows the prototype's port
(cerberus-lean-prototype/lean/CerbLean/Semantics/Step.lean:1441-1513, which
carries the same impl_mem cites). Divergences from the prototype, resolved
OCaml-ward:
  * failures are `MerrWIP` mem_errors with OCaml's exact strings —
    including the "not initiliased" (sic) spelling — via the shared
    Concrete.fail path (impl_mem.ml:540-546 → failReason); the prototype
    threw its own `typeError` strings.
  * the map stays the MemState assoc list (keyed lookup only, iteration
    never observed); the prototype used Std.HashMap in its own state.
Like OCaml (impl_mem.ml:2730 `(* TODO: check type is compatible *)`) and
the prototype alike, va_arg does NOT check the requested ctype against the
stored one — adding a check would diverge from the oracle.

The `IntMap.add`-on-existing-key updates (va_arg's index bump) are
replace-in-place on the assoc list; fresh-id inserts (va_start/va_copy)
are conses. -/

/-- IntMap.add on the varargs assoc list: replace any existing binding for
    `id`, else cons. -/
private def varargsAdd (id : Int) (v : Int × List (ctype × PointerValue))
    (m : List (Int × (Int × List (ctype × PointerValue)))) :
    List (Int × (Int × List (ctype × PointerValue))) :=
  if m.any (fun e => e.1 == id) then
    m.map (fun e => if e.1 == id then (id, v) else e)
  else
    (id, v) :: m

/-- va_start — impl_mem.ml:2698-2704: fresh id bound to (index 0, args),
    next_varargs_id bumped, returns `IV (Prov_none, id)`. -/
def vaStart (args : List (ctype × PointerValue)) : memM IntegerValue :=
  ND fun st =>
    let id := st.nextVarargsId
    (NDactive (.IV .Prov_none id),
     { st with varargs := varargsAdd id (0, args) st.varargs
               nextVarargsId := st.nextVarargsId + 1 })

/-- va_copy — impl_mem.ml:2706-2721: duplicate the (index, args) entry
    under a fresh id (the copy's index advances independently). Only a
    `Prov_none` integer is a valid va_list value. -/
def vaCopy (va : IntegerValue) : memM IntegerValue :=
  match va with
  | .IV .Prov_none id =>
    ND fun st =>
      match st.varargs.find? (fun e => e.1 == id) with
      | some (_, entry) =>
        let id' := st.nextVarargsId
        (NDactive (.IV .Prov_none id'),
         { st with varargs := varargsAdd id' entry st.varargs
                   nextVarargsId := st.nextVarargsId + 1 })
      | none => (NDkilled (failReason (MerrWIP "va_copy: not initiliased")), st)
  | _ => memFail (MerrWIP "va_copy: invalid va_list")

/-- va_arg — impl_mem.ml:2723-2741: read the pointer at the current index
    and ADVANCE the index (IntMap.add on the existing id). No ctype
    compatibility check, mirroring OCaml's TODO at :2730. -/
def vaArg (va : IntegerValue) (_ : ctype) : memM PointerValue :=
  match va with
  | .IV .Prov_none id =>
    ND fun st =>
      match st.varargs.find? (fun e => e.1 == id) with
      | some (_, (i, args)) =>
        match args[i.toNat]? with
        | some (_, ptr) =>
          (NDactive ptr,
           { st with varargs := varargsAdd id (i + 1, args) st.varargs })
        | none =>
          (NDkilled (failReason (MerrWIP "va_arg: invalid number of arguments")), st)
      | none => (NDkilled (failReason (MerrWIP "va_arg: not initiliased")), st)
  | _ => memFail (MerrWIP "va_arg: invalid va_list")

/-- va_end — impl_mem.ml:2743-2754: IntMap.remove of an initialised id. -/
def vaEnd (va : IntegerValue) : memM Unit :=
  match va with
  | .IV .Prov_none id =>
    ND fun st =>
      if st.varargs.any (fun e => e.1 == id) then
        (NDactive (), { st with varargs := st.varargs.filter (fun e => e.1 != id) })
      else
        (NDkilled (failReason (MerrWIP "va_end: not initiliased")), st)
  | _ => memFail (MerrWIP "va_end: invalid va_list")

/-- va_list — impl_mem.ml:2756-2764: retrieve the argument list for an id
    (the variadic-call consumer, formatted.lem:799 vsnprintf). OCaml
    `assert (n = 0)` (:2760, "not sure what happens with n <> 0") is an
    uncaught exception on the oracle — mirrored as a fail-stop (zero-
    discrepancy Z2-M-12, ruling Q4; this was a typed MerrOther kill, a
    different failure class). Unreachable from generated code: va_list is
    only applied to a fresh va_start id (index 0). -/
def vaList (vaIdx : Int) : memM (List (ctype × PointerValue)) :=
  ND fun st =>
    match st.varargs.find? (fun e => e.1 == vaIdx) with
    | some (_, (n, args)) =>
      if n == 0 then (NDactive args, st)
      else (NDkilled (CerbFail.failStopKill "va_list: assert (n = 0) failed (impl_mem.ml:2760)"), st)
    | none => (NDkilled (failReason (MerrWIP "va_list")), st)

/-! ### Misc -/

/-- copy_alloc_id — impl_mem.ml:2766-2770 (the RefinedC builtin,
    builtins.lem:470): the result pointer takes ADDRESS and PROVENANCE from
    the INTEGER — `intfromptr` runs on the pointer only for its range check
    (UB024 failure path included; both calls carry the OCaml's
    `Cerb_location.other "copy_alloc_id"`), then `ptrfromint ival`.
    zero-discrepancy Z-05 (noodle D4): this used to return `pv` unchanged
    (`Specified(1)` vs the oracle's `Specified(2)` on
    tests/immaculate/libc/zd-d4-copy-alloc-id.c). -/
def copyAllocId [LemFuel] [CerbGlobal.Switches] (enumDefs : EnumDefs) (tagDefs : TagDefs) (iv : IntegerValue) (pv : PointerValue) : memM PointerValue :=
  nd_bind (intfromptr enumDefs tagDefs (CerbLocation.other "copy_alloc_id") void (.Unsigned .Intptr_t) pv)
    (fun _ => ptrfromint (CerbLocation.other "copy_alloc_id") (.Unsigned .Intptr_t) void iv)
/-- call_intrinsic — impl_mem.ml:2190-2191 `assert false (* CHERI only *)`
    (zero-discrepancy Z-22; see the CHERI section note). -/
def callIntrinsic (_ : CerbLocation.Loc) (_ : String) (_ : List MemValue) : memM (Option MemValue) :=
  failStopMem "assert false (* CHERI only *): Concrete.call_intrinsic (impl_mem.ml:2190-2191)"

/-- Fuel-exhaustion sentinel for the fuel-threaded `Core_aux.zeros_aux`
    (arc-1): reached only past the default fuel's type-nesting depth, i.e.
    never for well-formed programs — same failure class as the existing
    failwith invariant branches. -/
/- Routed through the opaque fuelExhaustedWith (arc-3 audit F9): a plain
   `panic!` body is kernel-visible, making the fuel-exhausted branch
   provably equal to `default` — semantically false. Opaque core ⇒ no
   equations; still panics at runtime. -/
def zerosFuelExhausted (_ : Unit) : MemValue :=
  fuelExhaustedWith "Core_aux.zeros_aux: fuel exhausted" (MemValue.MVarray [])

end CerbMem
