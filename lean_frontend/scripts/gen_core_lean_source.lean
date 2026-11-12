import Lean
import Driver
open Lean Meta

/-! Generates the Core-to-Lean-source printers and symbol collectors:

* `CoreLeanSourceGen.lean`: `src_T`, rendering a value of each inductive type
  `T` in the closure of `generic_file` as Lean source that elaborates back
  to the same value;
* `CoreSymsGen.lean`: `col_T`, recording every `sym` a value mentions.

Library types (`List`, `Option`, `Prod`, `Pmap`, `Fmap`, primitives),
`sym` and `CerbLocation.Loc` have handwritten printers in
`CoreLeanSourceBase.lean`; `ctype` fields go through its `srcCtypeWith`
(named types). Rerun after a change to the Core types:

    cd lean_frontend && lake env lean scripts/gen_core_lean_source.lean

then copy both outputs to `generated/` (they are in
`handwritten_copy.manifest`). -/

def primitive : Std.HashMap Name String := Std.HashMap.ofList [
  (``Nat, "srcNat"), (``Int, "srcInt"), (``String, "srcString"), (``Bool, "srcBool"),
  (``Char, "srcChar"), (``UInt8, "srcUInt8"), (``UInt32, "srcUInt32"),
  (``Float, "srcFloat"), (``PUnit, "srcUnit"), (``Unit, "srcUnit")]

def poly1 : Std.HashMap Name String := Std.HashMap.ofList [
  (``List, "srcList"), (``Option, "srcOption"), (``Array, "srcArray")]

def fnName (n : Name) : String := "src_" ++ (n.toString.replace "." "_").replace "«" "" |>.replace "»" ""

partial def genFor (params : Array (FVarId × String)) (ty : Expr)
    (todo : IO.Ref (Array Name)) : MetaM String := do
  let ty ← whnfR ty
  let ty := ty.consumeMData
  if let .fvar id := ty then
    match params.find? (·.1 == id) with
    | some (_, p) => return p
    | none => throwError "unbound type variable {ty}"
  if ty.isForall then throwError "function-typed field {← ppExpr ty}"
  let .const n _ := ty.getAppFn | throwError "unsupported field type {← ppExpr ty}"
  let args := ty.getAppArgs
  if let some p := primitive[n]? then return p
  if n == ``CerbLocation.Loc then return "srcLoc"
  if n == ``sym then
    unless (← todo.get).contains ``symbol_description do todo.modify (·.push ``symbol_description)
    return "(srcSymWith (P.mk ty_src_symbol_description src_symbol_description))"
  if n == ``ctype then
    unless (← todo.get).contains ``ctype do todo.modify (·.push ``ctype)
    return "(srcCtypeWith (P.mk ty_src_ctype src_ctype))"
  if let some p := poly1[n]? then
    return s!"({p} {← genFor params args[0]! todo})"
  if n == ``Pmap then
    return s!"(srcPmap {← genFor params args[0]! todo} {← genFor params args[1]! todo})"
  if n == ``Prod then
    return s!"(srcProd {← genFor params args[0]! todo} {← genFor params args[1]! todo})"
  if n == ``Fmap then
    if (← whnfR args[1]!).getAppFn.constName? == some ``generic_fun_map_decl then
      return s!"(srcFunMap {← genFor params args[0]! todo} {← genFor params args[1]! todo})"
  if n == ``Fmap then
    -- the comparator is the key type's MapKeyType instance (Lem_Map)
    let k := args[0]!
    let kt := toString (← ppExpr k)
    return s!"(srcFmap (@Lem_Map.mapKeyCompare ({kt}) _) \"(@Lem_Map.mapKeyCompare ({kt}) _)\" {← genFor params k todo} {← genFor params args[1]! todo})"
  match (← getEnv).find? n with
  | some (.inductInfo _) =>
    unless (← todo.get).contains n do todo.modify (·.push n)
    let mut as := ""
    for a in args do
      if ← isType a then as := as ++ " " ++ (← genFor params a todo)
      else throwError "non-type parameter in {← ppExpr ty}"
    return s!"(P.mk (ty_{fnName n}{as}) ({fnName n}{as}))"
  | _ => throwError "unsupported type constant {n}"

def genPrinter (n : Name) (todo : IO.Ref (Array Name)) (tyDefs : IO.Ref (Array String)) : MetaM String := do
  let iv ← getConstInfoInduct n
  forallTelescopeReducing iv.type fun ps _ => do
    let mut params : Array (FVarId × String) := #[]
    let mut tyvars := ""
    let mut fargs := ""
    let mut i := 0
    for p in ps do
      unless ← isType p do throwError "non-type parameter of {n}"
      let tv := s!"τ{i}"; let f := s!"p{i}"
      params := params.push (p.fvarId!, f)
      tyvars := tyvars ++ s!" \{{tv} : Type}"
      fargs := fargs ++ s!" ({f} : P {tv})"
      i := i + 1
    let tyApp := s!"({n}" ++ String.join (List.range i |>.map (s!" τ{·}")) ++ ")"
    let tySrc := s!"\"({n}\"" ++ String.join (List.range i |>.map (s!" ++ \" \" ++ p{·}.ty")) ++ " ++ \")\""
    let mut alts := ""
    for c in iv.ctors do
      let ci ← getConstInfoCtor c
      let alt ← forallTelescopeReducing ci.type fun xs _ => do
        let fields := xs[iv.numParams:].toArray
        let vars := (List.range fields.size).map (s!"x{·}")
        let mut body := s!"app \"{c}\" ty"
        let mut j := 0
        for x in fields do
          let t ← inferType x
          if ← isProp t then throwError "proof field in {c}"
          -- substitute the constructor's parameter fvars by ours
          let t := t.replaceFVars xs[:iv.numParams] ps
          body := body ++ s!" |>.arg (({← genFor params t todo}).pr x{j})"
          j := j + 1
        let pat := if vars.isEmpty then s!"{c}" else s!"{c} " ++ " ".intercalate vars
        return s!"\n  | {pat} => {body} |>.done"
      alts := alts ++ alt
    let tyDef := s!"def ty_{fnName n}{tyvars}{fargs} : String := {tySrc}\n"
    tyDefs.modify (·.push tyDef)
    let tyCall := s!"(ty_{fnName n}" ++ String.join (List.range i |>.map (s!" p{·}")) ++ ")"
    return s!"partial def {fnName n}{tyvars}{fargs} : (_root_.{tyApp.drop 1} → Out{alts.replace " ty |>" s!" {tyCall} |>"}\n"

/-- Symbol-collecting traversal: `syms_T : T → Syms` visits every field and
records every `sym`. Types that cannot contain a `sym` are skipped. -/
partial def mentionsSym (seen : IO.Ref (Std.HashMap Name Bool)) (ty : Expr) : MetaM Bool := do
  let ty := (← whnfR ty).consumeMData
  if ty.isFVar then return true
  if ← isProp ty then return false
  let .const n _ := ty.getAppFn | return true
  if n == ``sym then return true
  if primitive.contains n || n == ``CerbLocation.Loc then return false
  for a in ty.getAppArgs do
    if (← isType a) then
      if ← mentionsSym seen a then return true
  match (← getEnv).find? n with
  | some (.inductInfo iv) =>
    if let some b := (← seen.get)[n]? then return b
    seen.modify (·.insert n false)
    let mut r := false
    for c in iv.ctors do
      let ci ← getConstInfoCtor c
      r := r || (← forallTelescopeReducing ci.type fun xs _ => do
        let mut r := false
        for x in xs[iv.numParams:] do
          r := r || (← mentionsSym seen (← inferType x))
        return r)
    seen.modify (·.insert n r)
    return r
  | _ => return false

partial def colFor (seen : IO.Ref (Std.HashMap Name Bool)) (params : Array (FVarId × String))
    (ty : Expr) (todo : IO.Ref (Array Name)) : MetaM String := do
  let ty := (← whnfR ty).consumeMData
  if let .fvar id := ty then
    match params.find? (·.1 == id) with
    | some (_, p) => return p
    | none => throwError "unbound type variable {ty}"
  unless ← mentionsSym seen ty do return "colNone"
  let .const n _ := ty.getAppFn | throwError "unsupported field type {← ppExpr ty}"
  let args := ty.getAppArgs
  if n == ``sym then return "colSym"
  if n == ``List then return s!"(colList {← colFor seen params args[0]! todo})"
  if n == ``Option then return s!"(colOption {← colFor seen params args[0]! todo})"
  if n == ``Prod then return s!"(colProd {← colFor seen params args[0]! todo} {← colFor seen params args[1]! todo})"
  if n == ``Pmap then return s!"(colPmap {← colFor seen params args[0]! todo} {← colFor seen params args[1]! todo})"
  if n == ``Fmap then return s!"(colFmap {← colFor seen params args[0]! todo} {← colFor seen params args[1]! todo})"
  unless (← todo.get).contains n do todo.modify (·.push n)
  let mut as := ""
  for a in args do as := as ++ " " ++ (← colFor seen params a todo)
  return s!"({colName n}{as})"
where colName (n : Name) : String := "col_" ++ ((fnName n).drop 4).toString

def genCollector (seen : IO.Ref (Std.HashMap Name Bool)) (n : Name) (todo : IO.Ref (Array Name)) : MetaM String := do
  let iv ← getConstInfoInduct n
  forallTelescopeReducing iv.type fun ps _ => do
    let mut params : Array (FVarId × String) := #[]
    let mut tyvars := ""
    let mut fargs := ""
    let mut i := 0
    for p in ps do
      let tv := s!"τ{i}"; let f := s!"p{i}"
      params := params.push (p.fvarId!, f)
      tyvars := tyvars ++ s!" \{{tv} : Type}"
      fargs := fargs ++ s!" ({f} : {tv} → Syms)"
      i := i + 1
    let tyApp := s!"({n}" ++ String.join (List.range i |>.map (s!" τ{·}")) ++ ")"
    let mut alts := ""
    for c in iv.ctors do
      let ci ← getConstInfoCtor c
      let alt ← forallTelescopeReducing ci.type fun xs _ => do
        let fields := xs[iv.numParams:].toArray
        let vars := (List.range fields.size).map (s!"x{·}")
        let mut body := "pure ()"
        let mut j := 0
        for x in fields do
          let t := (← inferType x).replaceFVars xs[:iv.numParams] ps
          let f ← colFor seen params t todo
          unless f == "colNone" do body := body ++ s!" *> {f} x{j}"
          j := j + 1
        let pat := if vars.isEmpty then s!"{c}" else s!"{c} " ++ " ".intercalate vars
        return s!"\n  | {pat} => {body}"
      alts := alts ++ alt
    return s!"partial def col_{((fnName n).drop 4).toString}{tyvars}{fargs} : (_root_.{tyApp.drop 1} → Syms{alts}\n"

#eval show MetaM Unit from do
  let seen ← IO.mkRef ({} : Std.HashMap Name Bool)
  let todo ← IO.mkRef (#[``generic_file] : Array Name)
  let mut out := ""
  let mut k := 0
  while k < (← todo.get).size do
    let n := (← todo.get)[k]!
    k := k + 1
    out := out ++ (← genCollector seen n todo) ++ "\n"
  let header := "-- Generated by scripts/gen_core_lean_source.lean; do not edit.\nimport CoreLeanSourceBase\n\nnamespace CoreLeanSource\n\nmutual\n\n"
  IO.FS.writeFile "CoreSymsGen.lean" (header ++ out ++ "end\n\nend CoreLeanSource\n")
  IO.println s!"{k} collectors"

#eval show MetaM Unit from do
  let todo ← IO.mkRef (#[``generic_file] : Array Name)
  let tyDefs ← IO.mkRef (#[] : Array String)
  let mut done : Array Name := #[]
  let mut out := ""
  let mut k := 0
  while k < (← todo.get).size do
    let n := (← todo.get)[k]!
    k := k + 1
    if n == ``Fmap || n == ``Pmap || n == ``CerbLocation.Loc || n == ``sym then continue
    out := out ++ (← genPrinter n todo tyDefs) ++ "\n"
    done := done.push n
  let header := "-- Generated by scripts/gen_core_lean_source.lean; do not edit.\nimport CoreLeanSourceBase\n\nnamespace CoreLeanSource\n\n"
  let tys := (← tyDefs.get).foldl (· ++ ·) ""
  IO.FS.writeFile "CoreLeanSourceGen.lean" (header ++ tys ++ "\nmutual\n\n" ++ out ++ "end\n\nend CoreLeanSource\n")
  IO.println s!"{done.size} printers"
