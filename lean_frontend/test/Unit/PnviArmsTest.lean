import CerbMem
import CerbFailProofs
import Lean.Elab.Command

/-! # PnviArmsTest — the PNVI-ae-udi arms and refusals of `CerbMem` (PNVI arc S3, 2026-10-07)

Record: `docs/2026-10-07_pnvi-s3-arms-record.md`; design record
`docs/2026-10-04_pnvi-ae-udi-design.md` §A.3, §D.4, §E S3, §G, §H.

Two kinds of witness, both on small hand-built states:

* **Runtime witnesses** (`checks`, run by `main` with the caller-selected fuel that
  `scripts/test_unit.sh` passes): each S3 arm's characteristic behaviour under
  `⟨[.PNVI .AE_UDI]⟩` — exposure on an integer cast, iota minting by `ptrfromint` at an
  ambiguous address, `resolve_iota` narrowing (and its SECOND failure), the symbolic
  load/store/kill/`validForDeref`/`eff_array_shift` arms, `eq_ptrval` across iotas,
  `diff_ptrval`'s collapse, load's expose-then-receipt — each with at least one control
  at the DEFAULT instance `⟨CerbGlobal.defaultSwitches⟩` showing the pre-S3 behaviour.
* **Refusal pins** (compile time; the build is RED if one fails): each refusal reachable
  by a closed term reduces, by `whnf`, to `failwithI (pnviRefusal d)` (or, for the two
  refusals ascribed at the memory monad, R-PNVI-08 and R-PNVI-10, to an `ND` elimination stuck on
  that leaf) whose detail `d`
  starts with its `R-PNVI-nn:` id — a refusal turned back into a mirror or a bare crash
  fails here (design §D.2 P7). The pure ones are also kernel `rfl` facts of the shape
  `… = failwithI (pnviRefusal _)`. A refusal aborts the process, so none is run.

No refusal is reachable at the default switch set (the record's §5); the runtime
controls at `⟨CerbGlobal.defaultSwitches⟩` exercise the default arms. No instance of
`CerbGlobal.Switches` or `LemFuel` is declared (rules W1/F2): every switch set and the
fuel are supplied with `letI` inside the helpers. -/

namespace PnviArmsTest
open CerbMem CerbFail CerberusImpl
set_option autoImplicit true

/-! ## Fixtures -/

/-- A named address-space top for the hand-built states (no literal cursor, rule A3). -/
def testTop : Int := 65536

def swDefault : CerbGlobal.Switches := ⟨CerbGlobal.defaultSwitches⟩
def swPlain : CerbGlobal.Switches := ⟨[.PNVI .PLAIN]⟩
def swAEUDI : CerbGlobal.Switches := ⟨[.PNVI .AE_UDI]⟩
def swPermissive : CerbGlobal.Switches := ⟨[.PNVI .AE_UDI, .pointer_arith .PERMISSIVE]⟩

def intTy : ctype := Ctype [] (.Basic (.Integer (.Signed .Int_)))
def ulongTy : ctype := Ctype [] (.Basic (.Integer (.Unsigned .Long)))
def tloc : CerbLocation.Loc := CerbLocation.unknown
def tags : CerbTags.TagDefsMap := default

/-- Two adjacent live allocations: id 0 = [100, 108), id 1 = [108, 116), taints chosen. -/
def twoAllocs (t0 t1 : Taint) : MemState :=
  { initialMemState testTop with
    allocations := ((Std.TreeMap.empty : Std.TreeMap Int Allocation).insert 0
        { base := 100, size := 8, taint := t0 }).insert 1 { base := 108, size := 8, taint := t1 } }

/-- The same state with an iota map (and `nextIota` past its keys). -/
def withIota (st : MemState) (entries : List (Int × IotaEntry)) : MemState :=
  { st with iotaMap := entries.foldl (fun m (k, v) => m.insert k v) Std.TreeMap.empty
            nextIota := entries.length }

def stU : MemState := twoAllocs .Unexposed .Exposed
def stE : MemState := twoAllocs .Exposed .Exposed

def sym (iota addr : Int) : PointerValue := .PV (.Prov_symbolic iota) (.PVconcrete none addr)
def some_ (id addr : Int) : PointerValue := .PV (.Prov_some id) (.PVconcrete none addr)

def provOf : PointerValue → Provenance | .PV p _ => p
def addrOf : PointerValue → Option Int | .PV _ (.PVconcrete _ a) => some a | _ => none
def isNull : PointerValue → Bool | .PV _ (.PVnull _) => true | _ => false
def taintOf (st : MemState) (id : Int) : Option Taint := (st.allocations.get? id).map (·.taint)
def iotaIs (st : MemState) (k : Int) (e : IotaEntry) : Bool := st.iotaMap.get? k == some e
def ivIs (iv : IntegerValue) (p : Provenance) (n : Int) : Bool :=
  match iv with | .IV p' n' => p' == p && n' == n

/-- The memory operations at an explicit switch set (`letI`, never an instance). -/
def ifp (sw : CerbGlobal.Switches) (pv : PointerValue) : CerbMem.memM IntegerValue :=
  letI := sw; intfromptr fmapEmpty tags tloc intTy (.Unsigned .Long) pv
def pfi (sw : CerbGlobal.Switches) (iv : IntegerValue) : CerbMem.memM PointerValue :=
  letI := sw; ptrfromint tloc (.Unsigned .Long) intTy iv
def ld [LemFuel] (sw : CerbGlobal.Switches) (ty : ctype) (pv : PointerValue) : CerbMem.memM (Footprint × MemValue) :=
  letI := sw; loadM fmapEmpty tags tloc ty pv
def kl (sw : CerbGlobal.Switches) (dyn : Bool) (pv : PointerValue) : CerbMem.memM Unit :=
  letI := sw; killM tloc dyn pv
def eqp (sw : CerbGlobal.Switches) (a b : PointerValue) : CerbMem.memM Bool :=
  letI := sw; eqPtrval tloc a b
def dfp [LemFuel] (sw : CerbGlobal.Switches) (a b : PointerValue) : CerbMem.memM IntegerValue :=
  letI := sw; diffPtrval fmapEmpty tags tloc intTy a b
def eas [LemFuel] (sw : CerbGlobal.Switches) (pv : PointerValue) (n : Int) : CerbMem.memM PointerValue :=
  letI := sw; effArrayShiftPtrval fmapEmpty tags tloc pv intTy (.IV .Prov_none n)

/-- Eight bytes holding the address 108 (little-endian) with provenance `Prov_some 1`,
    one whole-pointer copy (offsets 0..7): what storing `&obj1` leaves in memory. -/
def ptrTo1Bytes : List AbsByte :=
  ([108, 0, 0, 0, 0, 0, 0, 0] : List UInt8).zipIdx.map fun (v, i) =>
    { prov := .Prov_some 1, copyOffset := some (i : Int), value := some v }

def stBytes : MemState := writeBytesTo (twoAllocs .Exposed .Unexposed) 100 ptrTo1Bytes

/-! ## Runtime witnesses -/

def checks (fuel : Nat) : List (String × Bool) := Id.run do
  letI := LemFuel.mk fuel
  let r1 := step (ifp swAEUDI (some_ 0 104)) stU
  let r1d := step (ifp swDefault (some_ 0 104)) stU
  let r1p := step (ifp swPlain (some_ 0 104)) stU
  let r3 := step (pfi swAEUDI (.IV .Prov_none 108)) stE
  let r3d := step (pfi swDefault (.IV .Prov_none 108)) stE
  let stI := withIota stE [(0, .Double 0 1)]
  let rl := step (ld swAEUDI intTy (sym 0 108)) stI
  let stK := { stI with deadAllocations := [0] }
  let mv7 := MemValue.MVinteger (.Signed .Int_) (.IV .Prov_none 7)
  let rs := step (storeM fmapEmpty tags tloc intTy false (sym 0 108) mv7) stI
  let rk := step (kl swAEUDI false (sym 0 108)) stI
  let rx := step (ld swAEUDI ulongTy (some_ 0 100)) stBytes
  let rxd := step (ld swDefault ulongTy (some_ 0 100)) stBytes
  return [
    -- intfromptr (:2483-2505): exposure (AE ∨ AE_UDI) + mk_ival
    ("intfromptr AE_UDI: exposes the allocation, the integer has no provenance",
      (match r1.1 with | NDactive iv => ivIs iv .Prov_none 104 | _ => false) && taintOf r1.2 0 == some .Exposed),
    ("intfromptr PLAIN: mk_ival strips the provenance, NO exposure (the AE ∨ AE_UDI test)",
      (match r1p.1 with | NDactive iv => ivIs iv .Prov_none 104 | _ => false) && taintOf r1p.2 0 == some .Unexposed),
    ("intfromptr DEFAULT (control): IV (Prov_some 0) 104, no exposure",
      (match r1d.1 with | NDactive iv => ivIs iv (.Prov_some 0) 104 | _ => false) && taintOf r1d.2 0 == some .Unexposed),
    -- ptrfromint (:2190-2205): find_overlaping, after the exposure above
    ("ptrfromint AE_UDI after the cast's exposure: Prov_some 0",
      match (step (pfi swAEUDI (.IV .Prov_none 104)) r1.2).1 with
      | NDactive pv => provOf pv == .Prov_some 0 && addrOf pv == some 104 | _ => false),
    ("ptrfromint AE_UDI without exposure: Prov_none (require_exposed)",
      match (step (pfi swAEUDI (.IV .Prov_none 104)) stU).1 with
      | NDactive pv => provOf pv == .Prov_none | _ => false),
    ("ptrfromint AE_UDI ignores the integer's own provenance",
      match (step (pfi swAEUDI (.IV (.Prov_some 1) 104)) stU).1 with
      | NDactive pv => provOf pv == .Prov_none | _ => false),
    ("ptrfromint DEFAULT (control): the integer's provenance (PVI arm)",
      match (step (pfi swDefault (.IV (.Prov_some 0) 104)) stU).1 with
      | NDactive pv => provOf pv == .Prov_some 0 | _ => false),
    ("ptrfromint AE_UDI at an ambiguous address mints iota 0 = Double 0 1",
      (match r3.1 with | NDactive pv => provOf pv == .Prov_symbolic 0 && addrOf pv == some 108 | _ => false)
        && iotaIs r3.2 0 (.Double 0 1) && r3.2.nextIota == 1),
    ("ptrfromint DEFAULT (control) at the same address: Prov_none, no iota",
      (match r3d.1 with | NDactive pv => provOf pv == .Prov_none | _ => false) && r3d.2.iotaMap.isEmpty),
    ("ptrfromint AE_UDI of 0: PVnull",
      match (step (pfi swAEUDI (.IV .Prov_none 0)) stE).1 with | NDactive pv => isNull pv | _ => false),
    -- load, Prov_symbolic (:1662-1684): resolve_iota narrows Double 0 1 to the in-bounds 1
    ("load through iota 0 at 108: resolves to 1 (0 is out of bounds), collapses, last_used 1",
      (match rl.1 with | NDactive _ => true | _ => false) && iotaIs rl.2 0 (.Single 1) && rl.2.lastUsed == some 1),
    -- the two candidates fail with DIFFERENT kinds, so the reported error tells first from
    -- second (S3 review: one error kind for both could not): 116 is outside both [100, 108)
    -- and [108, 116); a dead candidate fails with DeadPtr (impl_mem.ml:1669), a live one
    -- outside its bounds with OutOfBoundPtr (:1673)
    ("load through iota 0 at 116, 0 dead (DeadPtr), 1 out of bounds (OutOfBoundPtr): the SECOND, OutOfBoundPtr, is reported",
      match (step (ld swAEUDI intTy (sym 0 116)) { stI with deadAllocations := [0] }).1 with
      | NDkilled r => r == failReason (MerrAccess LoadAccess OutOfBoundPtr) tloc | _ => false),
    ("load through iota 0 at 116, 0 out of bounds (OutOfBoundPtr), 1 dead (DeadPtr): the SECOND, DeadPtr, is reported",
      match (step (ld swAEUDI intTy (sym 0 116)) { stI with deadAllocations := [1] }).1 with
      | NDkilled r => r == failReason (MerrAccess LoadAccess DeadPtr) tloc | _ => false),
    -- kill, Prov_symbolic (:1518-1553)
    ("kill through iota 0 at 108: precondition 0 fails (addr ≠ base), 1 holds → 1 retired",
      (match rk.1 with | NDactive _ => true | _ => false) && rk.2.deadAllocations.contains 1
        && (rk.2.allocations.get? 1).isNone && iotaIs rk.2 0 (.Single 1)),
    ("kill through iota 0 at 112: 0 dead → Free_dead_allocation, 1 → Free_out_of_bound; the SECOND is reported",
      match (step (kl swAEUDI false (sym 0 112)) stK).1 with
      | NDkilled r => r == failReason (MerrUndefinedFree Free_out_of_bound) tloc | _ => false),
    ("kill DEFAULT (control): a live static Prov_some kill retires it",
      match step (kl swDefault false (some_ 0 100)) stE with
      | (NDactive _, s) => s.deadAllocations.contains 0 | _ => false),
    -- store, Prov_symbolic (:1771-1804)
    ("store through iota 0 at 108: resolves to 1, collapses, writes the bytes",
      (match rs.1 with | NDactive _ => true | _ => false) && iotaIs rs.2 0 (.Single 1) && rs.2.lastUsed == some 1
        && (readBytesFrom rs.2 108 1).map (·.value) == [some 7]),
    -- eq_ptrval, (Prov_symbolic, Prov_symbolic) (:1905-1914)
    ("eq_ptrval: iotas Single 1 / Single 1 at one address → true",
      match (step (eqp swAEUDI (sym 0 108) (sym 1 108)) (withIota stE [(0, .Single 1), (1, .Single 1)])).1 with
      | NDactive b => b | _ => false),
    ("eq_ptrval: iotas Single 0 / Single 1 → the provenance fork (msum)",
      match (step (eqp swAEUDI (sym 0 108) (sym 1 108)) (withIota stE [(0, .Single 0), (1, .Single 1)])).1 with
      | NDnd _ _ => true | _ => false),
    ("eq_ptrval: a Double iota is not Single → the fork",
      match (step (eqp swAEUDI (sym 0 108) (sym 1 108)) (withIota stE [(0, .Double 0 1), (1, .Single 1)])).1 with
      | NDnd _ _ => true | _ => false),
    ("eq_ptrval DEFAULT (control): equal Prov_some at one address → true",
      match (step (eqp swDefault (some_ 0 104) (some_ 0 104)) stE).1 with | NDactive b => b | _ => false),
    -- diff_ptrval (:2032-2105)
    ("diff_ptrval (iota Double 0 1 @112) - (Prov_some 1 @108) = 1, iota collapses to 1",
      match step (dfp swAEUDI (sym 0 112) (some_ 1 108)) stI with
      | (NDactive iv, s) => ivIs iv .Prov_none 1 && iotaIs s 0 (.Single 1) | _ => false),
    ("diff_ptrval (iota Single 1) - (iota Double 0 1): intersection Single 1, both collapse",
      match step (dfp swAEUDI (sym 0 112) (sym 1 108)) (withIota stE [(0, .Single 1), (1, .Double 0 1)]) with
      | (NDactive iv, s) => ivIs iv .Prov_none 1 && iotaIs s 0 (.Single 1) && iotaIs s 1 (.Single 1) | _ => false),
    ("diff_ptrval: disjoint iotas → MerrPtrdiff",
      match (step (dfp swAEUDI (sym 0 112) (sym 1 108)) (withIota stE [(0, .Single 0), (1, .Single 1)])).1 with
      | NDkilled r => r == failReason MerrPtrdiff tloc | _ => false),
    ("diff_ptrval: Double ∩ Double at ONE address → 0 (no refusal)",
      match (step (dfp swAEUDI (sym 0 108) (sym 1 108)) (withIota stE [(0, .Double 0 1), (1, .Double 0 1)])).1 with
      | NDactive iv => ivIs iv .Prov_none 0 | _ => false),
    ("diff_ptrval DEFAULT (control): different Prov_some → MerrPtrdiff",
      match (step (dfp swDefault (some_ 0 104) (some_ 1 108)) stE).1 with
      | NDkilled r => r == failReason MerrPtrdiff tloc | _ => false),
    -- validForDeref_ptrval (:2152-2163)
    ("validForDeref: iota Double 0 1 with 0 dead → do_test 1 → true",
      match (step (validForDerefPtrval fmapEmpty tags intTy (sym 0 108)) (withIota { stE with deadAllocations := [0] } [(0, .Double 0 1)])).1 with
      | NDactive b => b | _ => false),
    ("validForDeref: iota Single 0 with 0 dead → false",
      match (step (validForDerefPtrval fmapEmpty tags intTy (sym 0 108)) (withIota { stE with deadAllocations := [0] } [(0, .Single 0)])).1 with
      | NDactive b => !b | _ => false),
    -- eff_array_shift_ptrval (:2288-2400)
    ("eff_array_shift AE_UDI: Prov_some 0 + 2 ints = one past → allowed",
      match (step (eas swAEUDI (some_ 0 100) 2) stE).1 with
      | NDactive pv => provOf pv == .Prov_some 0 && addrOf pv == some 108 | _ => false),
    ("eff_array_shift AE_UDI: Prov_some 0 + 3 ints → MerrArrayShift (UB046)",
      match (step (eas swAEUDI (some_ 0 100) 3) stE).1 with
      | NDkilled r => r == failReason MerrArrayShift tloc | _ => false),
    ("eff_array_shift AE_UDI: Prov_none → MerrOther out-of-bound (Prov_none)",
      match (step (eas swAEUDI (.PV .Prov_none (.PVconcrete none 100)) 1) stE).1 with
      | NDkilled r => r == failReason (MerrOther "out-of-bound pointer arithmetic (Prov_none)") tloc | _ => false),
    ("eff_array_shift DEFAULT (control): Prov_some 0 + 3 ints → plain shift to 112",
      match (step (eas swDefault (some_ 0 100) 3) stE).1 with
      | NDactive pv => addrOf pv == some 112 | _ => false),
    ("eff_array_shift AE_UDI: iota Double 0 1 @108 + 1 int → only 1 admits it → collapse to 1",
      match step (eas swAEUDI (sym 0 108) 1) stI with
      | (NDactive pv, s) => provOf pv == Provenance.Prov_symbolic 0 && addrOf pv == some 112 && iotaIs s 0 (.Single 1) | _ => false),
    ("permissive symbolic shift keeps Double provenance outside both allocations",
      match step (eas swPermissive (sym 0 108) (-3)) stI with
      | (NDactive pv, st) => addrOf pv == some 96 && provOf pv == .Prov_symbolic 0
          && iotaIs st 0 (.Double 0 1)
      | _ => false),
    ("permissive shift accepts a concrete address without provenance",
      match (step (eas swPermissive (.PV .Prov_none (.PVconcrete none 100)) 1) stE).1 with
      | NDactive pv => addrOf pv == some 104 && provOf pv == .Prov_none
      | _ => false),
    ("permissive subtraction gives a scaled value without collapsing the iota",
      match step (dfp swPermissive (sym 0 112) (some_ 1 108)) stI with
      | (NDactive iv, st) => ivIs iv .Prov_none 1 && iotaIs st 0 (.Double 0 1)
      | _ => false),
    ("permissive subtraction of two symbolic pointers preserves both iotas",
      match step (dfp swPermissive (sym 0 108) (sym 1 112))
          (withIota stE [(0, .Double 0 1), (1, .Double 0 1)]) with
      | (NDactive iv, st) => ivIs iv .Prov_none (-1)
          && iotaIs st 0 (.Double 0 1) && iotaIs st 1 (.Double 0 1)
      | _ => false),
    ("eff_array_shift AE_UDI: iota Double 0 1 @108 + 0 → no collapse",
      match step (eas swAEUDI (sym 0 108) 0) stI with
      | (NDactive pv, s) => addrOf pv == some 108 && iotaIs s 0 (.Double 0 1) | _ => false),
    ("eff_array_shift AE_UDI: iota Single 0 @108 + 1 int → MerrArrayShift",
      match (step (eas swAEUDI (sym 0 108) 1) (withIota stE [(0, .Single 0)])).1 with
      | NDkilled r => r == failReason MerrArrayShift tloc | _ => false),
    -- load's expose_allocations (:1602-1606), BEFORE the receipt
    ("load AE_UDI of a stored &obj1 as an integer exposes allocation 1; the integer has no provenance",
      (match rx.1 with | NDactive (_, .MVinteger _ iv) => ivIs iv .Prov_none 108 | _ => false)
        && taintOf rx.2 1 == some .Exposed && rx.2.lastUsed == some 0),
    ("load DEFAULT (control): no exposure, the integer keeps Prov_some 1",
      (match rxd.1 with | NDactive (_, .MVinteger _ iv) => ivIs iv (.Prov_some 1) 108 | _ => false)
        && taintOf rxd.2 1 == some .Unexposed) ]

/-! ## Refusal pins (compile time)

`refusalId e` = `some id` iff `whnf e` is `failwithI (pnviRefusal d)` and `d`'s leading
literal starts with `id ++ ":"` (an interpolated `d` contributes its first literal). -/

section Pins
open Lean Meta Elab Command Term

partial def leadingLit (e : Expr) : MetaM (Option String) := do
  let e ← instantiateMVars e
  match e with
  | .lit (.strVal s) => return some s
  | .mdata _ b => leadingLit b
  | _ =>
    if e.isAppOfArity ``HAppend.hAppend 6 then leadingLit (e.getArg! 4)
    else if e.isAppOfArity ``String.append 2 then leadingLit (e.getArg! 0)
    else if e.isAppOfArity ``ToString.toString 3 then leadingLit (e.getArg! 2)
    else return none

/-- `some d` iff `e` reduces (`whnf`) to `failwithI (pnviRefusal d)`. -/
def refusalLeaf? (e : Expr) : MetaM (Option String) := do
  let e ← whnf e
  unless e.isAppOfArity ``failwithI 3 do return none
  let msg ← instantiateMVars (e.getArg! 2)
  unless msg.isAppOfArity ``CerbMem.pnviRefusal 1 do return none
  leadingLit msg.appArg!

/-- The refusal a term reduces to: either the leaf itself, or — for the refusals ascribed
    at the memory monad (`CerbMem.pnviRefuseM`, R-PNVI-08 and R-PNVI-10; S4 Part 1) — an elimination
    (a `match`/`casesOn` on `ND`) that is STUCK on such a leaf: its head is a matcher or a
    `casesOn` and one of its arguments reduces to the leaf. Anything else is `none`. -/
def refusalDetail? (e : Expr) : MetaM (Option String) := do
  let e ← whnf e
  if let some d ← refusalLeaf? e then return some d
  let some head := e.getAppFn.constName? | return none
  unless (← Lean.Meta.isMatcher head) || head.isStr && head.getString! == "casesOn" do return none
  for a in e.getAppArgs do
    if let some d ← refusalLeaf? a then return some d
  return none

/-- Fails the build unless `t` reduces to the refusal `id` (or, with `id = ""`, to a
    NON-refusal — the negative controls). -/
def pin (id : String) (t : Term) : CommandElabM Unit := do
  let d? ← liftTermElabM do
    let e ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    -- a fuel'd pin is stated for EVERY fuel `fun k => …` (no fuel numeral, rule F1-F6):
    -- the body is reduced with `k` a free variable
    lambdaTelescope (← instantiateMVars e) fun _ b => refusalDetail? b
  match id, d? with
  | "", none => pure ()
  | "", some d => throwError "PnviArmsTest: a negative control reduced to a PNVI refusal: {d}"
  | _, some d =>
    unless d.startsWith (id ++ ":") do throwError "PnviArmsTest: expected refusal {id}, got detail {d}"
  | _, none => throwError "PnviArmsTest: {id} — the term does not reduce to `failwithI (pnviRefusal …)` (a mirror or a bare crash?)"

/-- The provenance of a reconstructed pointer (for `R-PNVI-05`, whose refusal is the provenance). -/
def ptrProv : MemValue → Provenance
  | .MVpointer _ (.PV p _) => p
  | _ => .Prov_none

def ptrTy : ctype := Ctype [] (.Pointer no_qualifiers intTy)
/-- Eight bytes encoding 0x1000 with no provenance and no copy offsets (`NotValidPtrProv`). -/
def ptrBytes : List AbsByte := ([0x00, 0x10, 0, 0, 0, 0, 0, 0] : List UInt8).map fun v => { value := some v }
def closureDouble : Address → OverlapResult := fun _ => .DoubleAlloc 0 1
/-- Three candidates at 108 under AE_UDI: one-past of id 0, one-past of the empty id 1 at
    108, inside id 2 (all exposed). -/
def stThree : MemState :=
  { initialMemState testTop with
    allocations := (((Std.TreeMap.empty : Std.TreeMap Int Allocation).insert 0
        { base := 100, size := 8, taint := .Exposed }).insert 1 { base := 108, size := 0, taint := .Exposed }).insert 2
        { base := 108, size := 8, taint := .Exposed } }

run_cmd pin "R-PNVI-01" (← `(combineProv (.Prov_symbolic 0) .Prov_none))
run_cmd pin "R-PNVI-01" (← `(combineProv (.Prov_some 3) (.Prov_symbolic 0)))
run_cmd pin "R-PNVI-03" (← `(@findOverlapping swAEUDI stThree 108))
run_cmd pin "R-PNVI-04" (← `(lookupIota stE 5))
run_cmd pin "R-PNVI-05" (← `(ptrProv (@reconstructValueAbst swAEUDI fmapEmpty default closureDouble [] [] 0 ptrTy ptrBytes).2))
run_cmd pin "R-PNVI-06" (← `(fun (k : Nat) => @arrayShiftPtrval ⟨k⟩ fmapEmpty default (sym 0 108) intTy (.IV .Prov_none 1)))
run_cmd pin "R-PNVI-07" (← `(casePtrval (α := Nat) (sym 0 108) (fun _ => 0) (fun _ => 1) (fun _ _ => 2)))
run_cmd pin "R-PNVI-08" (← `(fun (k : Nat) => step (@dfp ⟨k⟩ swAEUDI (sym 0 108) (sym 1 112)) (withIota stE [(0, .Double 0 1), (1, .Double 0 1)])))
run_cmd pin "R-PNVI-10" (← `(fun (k : Nat) => step (@eas ⟨k⟩ swAEUDI (sym 0 104) 1) (withIota (twoAllocs .Exposed .Exposed) [(0, .Double 0 1)])))
-- negative controls: the checker does not call a mirror or the default-path crash a refusal
run_cmd pin "" (← `(combineProv .Prov_none .Prov_none))
run_cmd pin "" (← `(casePtrval (α := Nat) (.PV .Prov_device (.PVconcrete none 0xABC)) (fun _ => 0) (fun _ => 1) (fun _ _ => 2)))

end Pins

-- kernel facts of the refusal SHAPE (the pure sites)
example : ∃ d, combineProv (.Prov_symbolic 0) .Prov_none = failwithI (pnviRefusal d) := ⟨_, rfl⟩
example : ∃ d, combineProv .Prov_none (.Prov_symbolic 0) = failwithI (pnviRefusal d) := ⟨_, rfl⟩
example : ∃ d, lookupIota stE 5 = failwithI (pnviRefusal d) := ⟨_, rfl⟩
example : ∃ d, casePtrval (α := Nat) (sym 0 108) (fun _ => 0) (fun _ => 1) (fun _ _ => 2) = failwithI (pnviRefusal d) := ⟨_, rfl⟩

end PnviArmsTest

def main (args : List String) : IO UInt32 := do
  let some fuel := (args.head? >>= String.toNat?) | do
    IO.eprintln "pnvi-arms-test requires caller-selected fuel"; return 2
  let cs := PnviArmsTest.checks fuel
  let mut failed := 0
  for (name, ok) in cs do
    if ok then IO.println s!"  ok   {name}" else
      IO.println s!"  FAIL {name}"; failed := failed + 1
  IO.println "PnviArmsTest: 9 refusal pins (R-PNVI-01 ×2, -03, -04, -05, -06, -07, -08, -10) + 2 negative controls checked at compile time"
  IO.println s!"PnviArmsTest: {cs.length - failed}/{cs.length} runtime witnesses passed"
  return (if failed == 0 then 0 else 1)
