import Lean
import JonnyLean

/-!
Machine-readable audit of the imported JonnyLean environment.

The module list comes from Lean's import table, and declaration ownership comes
from Lean's constant-to-module table. In particular, neither namespace spelling
nor reachability from a selected theorem determines which declarations are
audited. This includes private declarations, unused axioms, generated constants,
and imported modules containing no declarations.

Lean's `collectAxioms` follows the types and values in the checked environment.
The consumer of this report is responsible for applying an axiom policy.
-/

namespace JonnyLeanAudit

private def isProjectModule (name : Lean.Name) : Bool :=
  (`JonnyLean).isPrefixOf name

private def declarationKind : Lean.ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def sortedNames (names : Array Lean.Name) : Array Lean.Name :=
  names.qsort fun a b => a.toString < b.toString

private def namesJson (names : Array Lean.Name) : Lean.Json :=
  .arr <| (sortedNames names).map fun name => .str name.toString

private def report : Lean.MetaM Lean.Json := do
  let env ← Lean.getEnv
  let moduleNames := env.header.moduleNames
  let modules := moduleNames.filter isProjectModule
  let constants := env.checked.get.constants.toList.toArray.qsort fun a b =>
    a.1.toString < b.1.toString
  let mut declarations := #[]
  for (name, info) in constants do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    let some moduleName := moduleNames[moduleIdx.toNat]? | continue
    unless isProjectModule moduleName do continue
    let type ← Lean.Meta.ppExpr info.type
    let axioms ← Lean.collectAxioms name
    declarations := declarations.push <| Lean.Json.mkObj [
      ("name", .str name.toString),
      ("module", .str moduleName.toString),
      ("kind", .str <| declarationKind info),
      ("type", .str type.pretty),
      ("axioms", namesJson axioms)
    ]
  return Lean.Json.mkObj [
    ("modules", namesJson modules),
    ("declarations", .arr declarations)
  ]

end JonnyLeanAudit

set_option pp.fullNames true in
run_cmd do
  let result ← Lean.Elab.Command.liftTermElabM JonnyLeanAudit.report
  Lean.Elab.Command.liftIO <| IO.println s!"JONNYLEAN_AUDIT={result.compress}"
