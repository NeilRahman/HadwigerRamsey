import HadwigerRamsey.Ramsey

open Lean
namespace HadwigerRamsey.Ramsey.Audit

run_cmd do
  let env ← getEnv
  for (source, target) in
      [(``HadwigerRamsey.Ramsey.eventually_floor_lt_ramsey, ``HadwigerRamsey.existencethm),
       (``HadwigerRamsey.Ramsey.eventually_ramsey_le_ceil, ``HadwigerRamsey.mainthm),
       (``HadwigerRamsey.theorem1_1, ``HadwigerRamsey.Ramsey.eventually_floor_lt_ramsey),
       (``HadwigerRamsey.theorem1_1, ``HadwigerRamsey.Ramsey.eventually_ramsey_le_ceil)] do
    let some info := env.find? source | throwError "Missing declaration {source}"
    let some value := info.value? (allowOpaque := true) | throwError "Missing proof of {source}"
    unless value.getUsedConstants.contains target do
      throwError "Required manuscript dependency is missing: {source} → {target}"
    logInfo m!"Explicit manuscript dependency: {source} → {target}"

end HadwigerRamsey.Ramsey.Audit
