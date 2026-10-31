import HadwigerRamsey.OptApprox
open Lean

namespace HadwigerRamsey.OptApprox.Audit

private def dependencyPath (env : Environment) (target : Name) : Nat → Name → Option (List Name)
  | 0, _ => none
  | fuel+1, name =>
    if name == target then some [name]
    else if !name.toString.startsWith "HadwigerRamsey" then none
    else do
      let info ← env.find? name
      let value ← info.value?
      value.getUsedConstants.toList.findSome? (fun dep =>
        (dependencyPath env target fuel dep).map (name :: ·))

run_cmd do
  let env ← getEnv
  match dependencyPath env ``HadwigerRamsey.opt 32 ``HadwigerRamsey.optapprox with
  | none => throwError "The endpoint does not depend on the public opt theorem"
  | some path => logInfo m!"Explicit theorem dependency: {path}"

end HadwigerRamsey.OptApprox.Audit
