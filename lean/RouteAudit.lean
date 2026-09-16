import LiouvilleGoldbach
import Lean.Util.FoldConsts

set_option maxHeartbeats 0

/- Inspect the project's transitive proof dependencies to ensure the final
theorem follows the new route and does not silently reuse the replaced lemmas. -/
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[`LiouvilleGoldbach.liouville_goldbach]
  let mut seen : Lean.NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name
      | throwError "Missing declaration during dependency audit: {name}"
    for dep in info.getUsedConstantsAsSet.toArray do
      if (`LiouvilleGoldbach).isPrefixOf dep then
        pending := pending.push dep
  let required := #[
    `LiouvilleGoldbach.IntervalSigns.commuting_completion_two,
    `LiouvilleGoldbach.IntervalSigns.commuting_completion_three,
    `LiouvilleGoldbach.defect_commuting_square,
    `LiouvilleGoldbach.uniform_even_descent,
    `LiouvilleGoldbach.extension_descent_certificate_symmetric,
    `LiouvilleGoldbach.short_representative_of_invariance,
    `LiouvilleGoldbach.half_interval_extension_via_invariance,
    `LiouvilleGoldbach.Final.exists_prime_square_below_half,
    `LiouvilleGoldbach.Final.no_multiplicative_agreement_of_odd]
  for name in required do
    unless seen.contains name do
      throwError "The polished proof does not use the expected declaration: {name}"
  let replaced := #[
    `LiouvilleGoldbach.IntervalSigns.quarterBand,
    `LiouvilleGoldbach.IntervalSigns.centralBand,
    `LiouvilleGoldbach.oddCompletion_two,
    `LiouvilleGoldbach.oddCompletion_three,
    `LiouvilleGoldbach.extension_descent_certificate,
    `LiouvilleGoldbach.half_interval_extension,
    `LiouvilleGoldbach.Final.no_multiplicative_agreement]
  for name in replaced do
    if seen.contains name then
      throwError "The polished proof still depends on a replaced declaration: {name}"
  Lean.logInfo "Polished proof route verified: all nine new ingredients occur, and all seven replaced ingredients are absent."
