import HadwigerRamsey.UnequalBipMinor

open Lean
namespace HadwigerRamsey.UnequalBipMinorAudit

run_cmd do
  let env ← getEnv
  let source := ``HadwigerRamsey.unequalBipMinor
  let some info := env.find? source | throwError "Missing declaration {source}"
  let some value := info.value? (allowOpaque := true) | throwError "Missing proof of {source}"
  for target in [``HadwigerRamsey.bipMinor, ``HadwigerRamsey.Main.cross_minor_unequal] do
    unless value.getUsedConstants.contains target do
      throwError "Required manuscript dependency is missing: {source} → {target}"
    logInfo m!"Explicit Corollary 3.4 dependency: {source} → {target}"

end HadwigerRamsey.UnequalBipMinorAudit
