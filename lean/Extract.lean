import Lean
open Lean

/-!
# pluck-extract

Reads compiled Lean modules **one at a time, without loading their imports**, straight from
their `.olean`, `.olean.server` and `.olean.private` parts (as `leanchecker` does), and prints
one JSON line per module and per constant.

Usage:
  pluck-extract graph            < lines "Module.Name<TAB>/path/to/Module.olean"
  pluck-extract stmt NAME BASE   # binders of one constant's type, for the closure report

Records (one JSON object per line):
  {"t":"mod","m":…,"isModule":…,"imports":[[mod,pub,meta,all]…],"extra":[[mod,pub,meta]…],
   "exts":{extName:count…},"aux":[extraConstNames…]}
  {"t":"c","m":…,"n":…,"k":kind,"ty":[consts…],"val":[consts…],"rp":returnsProp,
   "rng":[line,col,endLine,endCol]?,"tsz":typeSize,"vsz":valueSize,"ctors":[…]?,"induct":…?}
-/

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

/-- Does the type end (after all `∀`) in `Prop`? Then constants of this type build
propositions: predicates, relations, `Prop`-valued structures. -/
partial def returnsProp : Expr → Bool
  | .forallE _ _ b _ => returnsProp b
  | .mdata _ e => returnsProp e
  | .sort u => u.isZero
  | _ => false

/-- Number of nodes, capped, as a cheap size measure. Uses the DAG, so shared subterms count once. -/
def exprSize (e : Expr) : Nat := e.approxDepth.toNat + (e.getUsedConstants.size)

def nameJ (n : Name) : Json := Json.str n.toString

def usedJ (e : Expr) : Json := Json.arr (e.getUsedConstants.map nameJ)

def rangeJ (r : DeclarationRanges) : Json :=
  Json.arr #[r.range.pos.line, r.range.pos.column, r.range.endPos.line, r.range.endPos.column]

/-- The olean parts of one module, most private last. -/
def partFiles (base : System.FilePath) : IO (Array System.FilePath) := do
  let mut fs := #[base]
  for lvl in [OLeanLevel.server, OLeanLevel.private] do
    let f := lvl.adjustFileName base
    if ← f.pathExists then fs := fs.push f
  return fs

unsafe def extractModule (mod : String) (base : System.FilePath) (out : IO.FS.Stream) : IO Unit := do
  let parts ← readModuleDataParts (← partFiles base)
  let last := parts[parts.size - 1]!.1
  -- declaration ranges and extension statistics, merged over all parts
  let mut ranges : NameMap DeclarationRanges := {}
  let mut exts : Std.HashMap String Nat := {}
  let mut extra : Array Json := #[]
  for (md, _) in parts do
    for (ext, es) in md.entries do
      if es.size > 0 then
        exts := exts.insert ext.toString (max (exts.getD ext.toString 0) es.size)
      if ext == `Lean.declRangeExt then
        for e in es do
          let (n, r) : Name × DeclarationRanges := unsafeCast e
          ranges := ranges.insert n r
      if ext == `Lean.extraModUses then
        for e in es do
          let u : ExtraModUse := unsafeCast e
          extra := extra.push (Json.arr #[nameJ u.module, u.isExported, u.isMeta])
  let imports := last.imports.map fun i =>
    Json.arr #[nameJ i.module, i.isExported, i.isMeta, i.importAll]
  let modRec := Json.mkObj [
    ("t", "mod"), ("m", mod), ("isModule", last.isModule),
    ("imports", Json.arr imports), ("extra", Json.arr extra),
    ("exts", Json.mkObj (exts.toList.map fun (k, v) => (k, (v : Json)))),
    ("aux", Json.arr (last.extraConstNames.map nameJ))]
  out.putStrLn modRec.compress
  for ci in last.constants do
    let val? := ci.value? (allowOpaque := true)
    let mut fields : List (String × Json) := [
      ("t", "c"), ("m", mod), ("n", nameJ ci.name), ("k", kindOf ci),
      ("ty", usedJ ci.type), ("rp", returnsProp ci.type),
      ("tsz", exprSize ci.type), ("th", toString ci.type.hash),
      ("lps", Json.arr (ci.levelParams.toArray.map nameJ))]
    if let some v := val? then
      fields := fields ++ [("val", usedJ v), ("vsz", exprSize v)]
    match ci with
    | .inductInfo v => fields := fields ++ [("ctors", Json.arr (v.ctors.toArray.map nameJ)),
                                            ("all", Json.arr (v.all.toArray.map nameJ))]
    | .ctorInfo v => fields := fields ++ [("induct", nameJ v.induct)]
    | .recInfo v =>
      -- recursor rules mention the constructors; record them as value dependencies
      let rs := v.rules.toArray.foldl (init := (∅ : NameSet)) fun s r =>
        r.rhs.getUsedConstants.foldl (·.insert ·) (s.insert r.ctor)
      fields := fields ++ [("val", Json.arr (rs.toArray.map nameJ))]
    | _ => pure ()
    if let some r := ranges.find? ci.name then
      fields := fields ++ [("rng", rangeJ r)]
    out.putStrLn (Json.mkObj fields).compress
  -- Region freeing is skipped on purpose: nothing may reference the module data afterwards,
  -- and keeping that invariant across `unsafeCast` is not worth the risk. The OS maps the
  -- files lazily, so resident memory stays near the size of the module being read.

/-- Strip binders of a type and report each one: what the theorem *takes*. -/
unsafe def stmt (name : Name) (base : System.FilePath) (out : IO.FS.Stream) : IO Unit := do
  let parts ← readModuleDataParts (← partFiles base)
  let last := parts[parts.size - 1]!.1
  let some ci := last.constants.find? (·.name == name)
    | throw <| IO.userError s!"{name} not found in {base}"
  let rec go (e : Expr) (acc : Array Json) : Array Json × Expr :=
    match e with
    | .forallE n t b bi =>
      let head := (t.getForallBody.getAppFn.constName?.map nameJ).getD Json.null
      let j := Json.mkObj [("name", nameJ n), ("bi", toString (repr bi)),
        ("head", head), ("uses", usedJ t), ("dbg", String.mk ((toString t).toList.take 400))]
      go b (acc.push j)
    | .mdata _ e => go e acc
    | e => (acc, e)
  let (bs, concl) := go ci.type #[]
  let j := Json.mkObj [("t", "stmt"), ("n", nameJ name), ("k", kindOf ci),
    ("binders", Json.arr bs),
    ("concl", Json.mkObj [("head", (concl.getAppFn.constName?.map nameJ).getD Json.null),
                          ("uses", usedJ concl), ("dbg", String.mk ((toString concl).toList.take 600))])]
  out.putStrLn j.compress

unsafe def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  match args with
  | ["graph"] =>
    let stdin ← IO.getStdin
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      match (String.mk (line.toList.filter (fun c => c != '\n' && c != '\r'))).splitOn "\t" with
      | [mod, path] =>
        try extractModule mod path out
        catch e => out.putStrLn (Json.mkObj [("t", "err"), ("m", mod), ("e", toString e)]).compress
      | _ => pure ()
      out.flush
    return 0
  | ["stmt", n, base] => stmt n.toName base out; return 0
  | _ =>
    IO.eprintln "usage: pluck-extract graph < module-list | pluck-extract stmt NAME OLEAN"
    return 2
