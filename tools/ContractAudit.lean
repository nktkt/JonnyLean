/- Appended to a temporary copy of a contract after its normal strict compilation.
   The wrapper imports Lean so this command can inspect all local declarations.
   No project or contract source is modified. Imported mathematical declarations
   are separately covered by Audit.lean. -/
set_option pp.fullNames true in
run_cmd do
  let env ← Lean.getEnv
  let result ← Lean.Elab.Command.liftTermElabM do
    let mut rows := #[]
    for (name, info) in env.checked.get.constants.toList do
      if (env.getModuleIdxFor? name).isSome then continue
      let axioms ← Lean.collectAxioms name
      let type ← Lean.Meta.ppExpr info.type
      let kind := match info with
        | .axiomInfo _ => "axiom"
        | .thmInfo _ => "theorem"
        | _ => "other"
      rows := rows.push <| Lean.Json.mkObj [
        ("name", .str name.toString), ("kind", .str kind), ("type", .str type.pretty),
        ("axioms", .arr <| axioms.map fun a => .str a.toString)]
    return Lean.Json.mkObj [("declarations", .arr rows)]
  Lean.Elab.Command.liftIO <| IO.println s!"JONNYLEAN_CONTRACT_AUDIT={result.compress}"
