import HadwigerRamsey.Main

open Lean
namespace HadwigerRamsey.Main.Audit

run_cmd do
  let env ← getEnv
  let source := ``HadwigerRamsey.Main.mainthm_small
  let some info := env.find? source | throwError "Missing declaration {source}"
  let some value := info.value? (allowOpaque := true) | throwError "Missing proof of {source}"
  for target in [``HadwigerRamsey.twobigsets, ``HadwigerRamsey.connectedsets,
      ``HadwigerRamsey.bipMinor, ``HadwigerRamsey.denseMinor,
      ``HadwigerRamsey.thomasonupper, ``HadwigerRamsey.optapprox] do
    unless value.getUsedConstants.contains target do
      throwError "Required manuscript dependency is missing: {source} → {target}"
    logInfo m!"Explicit manuscript dependency: {source} → {target}"

end HadwigerRamsey.Main.Audit
