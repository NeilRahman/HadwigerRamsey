import HadwigerRamsey.TwoBigSets

open Lean
namespace HadwigerRamsey.TwoBigSets.Audit

run_cmd do
  let env ← getEnv
  for (source, target) in [
      (``HadwigerRamsey.twobigsets, ``HadwigerRamsey.connectedsets),
      (``HadwigerRamsey.twobigsets, ``HadwigerRamsey.bipMinor),
      (``HadwigerRamsey.twobigsets, ``HadwigerRamsey.TwoBigSets.large_separated_sets),
      (``HadwigerRamsey.TwoBigSets.large_separated_sets, ``HadwigerRamsey.bigset)] do
    let some info := env.find? source | throwError "Missing declaration {source}"
    let some value := info.value? (allowOpaque := true) | throwError "Missing proof of {source}"
    unless value.getUsedConstants.contains target do
      throwError "Required proof dependency is missing: {source} → {target}"
    logInfo m!"Explicit theorem dependency: {source} → {target}"

end HadwigerRamsey.TwoBigSets.Audit
