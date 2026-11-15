import Lean

/-!
Extract the actual compiled types of the 17 unchanged endpoint/consumer
theorems from the authorized remote environment. Import at the private level;
the private Colouring theorem is addressed by its exact compiled name.

The encoding retains the complete kernel expression structure, constants,
universe structure, de Bruijn indices, binder information, literal values,
let nonDep flags, and projections. Binder names are ignored; universe parameter
names are replaced by their positions in the declaration's ordered parameter
list; semantically inert Expr.mdata nodes are erased. No unfolding, reduction,
pretty-printing, alpha-guessing, or proof comparison is performed.

Unexpected free variables, expression/universe metavariables, or undeclared
universe parameters cause extraction to fail. JSON arrays use explicit tags,
including for Name.str versus Name.num components, so the representation does
not depend on potentially ambiguous pretty-printed names.

Run only through SSH:
  lake env lean --run ExtractRefactorTypes.lean OUTPUT.json
-/

open Lean

namespace RefactorTypeAudit

def dottedName (s : String) : Name :=
  (s.splitOn ".").foldl (fun baseName component =>
    match component.toNat? with
    | some n => .num baseName n
    | none => .str baseName component) .anonymous

def theoremNames : Array Name := #[
  `ClauseBound.Group.Sample.avg_exp_le,
  `ClauseBound.Group.card_sample_tail_le,
  `ClauseBound.Rec.Tail.two_point_le,
  `ComplexityAbstracts.SubexponentialSATAbstract.not_eth,
  `Eight.ViaGrouping.Table.sum_map_le,
  `EthBridge.Anthropic.not_eth_of_ethIsFalse,
  `EthBridge.AnthropicChain.not_eth,
  `EthBridge.OpenAIChain.not_eth,
  `EthBridge.Shared.BernoulliMGF.bernoulli_mgf_le,
  `EthBridge.Shared.BoundedMGF.weighted_exp_le,
  `EthBridge.Shared.BoundedMGF.weighted_mgf_le,
  `EthBridge.Shared.FiniteConcentration.exp_mul_abs_le,
  `EthBridge.Shared.FiniteConcentration.sum_indicator_le_of_abs_mgf,
  `EthBridge.Shared.FiniteConcentration.sum_indicator_le_of_mgf,
  `EthBridge.Shared.FiniteConcentration.sum_indicator_mul_exp_le,
  `EthBridge.Shared.FiniteMoments.square_sum_indicator,
  `EthBridge.Shared.FiniteMoments.sum_affine_square,
  `EthBridge.Shared.FiniteMoments.sum_centered_square,
  `EthBridge.Shared.FiniteMoments.sum_square_indicator,
  `EthBridge.Shared.FiniteProduct.sum_defaultFilled_prod,
  `EthBridge.Shared.FiniteProduct.sum_piFinset_prod,
  `EthBridge.Shared.FiniteProduct.sum_prod_eq_prod_sum,
  `EthBridge.Shared.FiniteSampling.average_restrict,
  `EthBridge.Shared.FiniteSampling.card_restrict_mul,
  `EthBridge.Shared.FiniteSampling.exists_avoiding_of_budget,
  `EthBridge.Shared.FiniteSampling.sum_restrict,
  `EthBridge.Shared.FiniteSampling.sum_restrict_mul_card,
  `EthBridge.Shared.TensorContraction.tensor_inverse,
  `EthBridge.Shared.WeightedOverlap.sum_kernel_le_of_dependency_sets,
  `EthBridge.Shared.WeightedOverlap.sum_kernel_le_of_weighted_overlap,
  `EthBridge.WordRAM.not_eth_ram,
  `Fintype.card_product_filter_lt,
  `Groundwork.Colouring.exists_colouring_fintype,
  `Groundwork.Grid.prod_eq_factorised,
  `Groundwork.PB.add,
  `Groundwork.PB.bound_comp,
  `Groundwork.PB.bound_le,
  `Groundwork.PB.comp,
  `Groundwork.PB.const,
  `Groundwork.PB.id',
  `Groundwork.PB.mono_bound,
  `Groundwork.PB.mul,
  `Groundwork.PB.pow,
  `Groundwork.PolyT.bval_bits,
  `Groundwork.PolyT.bval_lt,
  `Groundwork.Prog.NetE.le_foldr_max,
  `Groundwork.card_pairs,
  `Groundwork.ofWord_lt,
  `Groundwork.prod_factorised,
  `Groundwork.sum_tuples_prod,
  `MainResults.ethIsFalse,
  `OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport.bits_value,
  `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value_eq_toNat,
  `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleOdometer.value_lt_power_length,
  `OAI.Algorithms.SubexponentialSAT.ModularArithmetic.toNat_lt_pow_length,
  `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial.ordinary_add,
  `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial.ordinary_const,
  `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial.ordinary_id,
  `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial.ordinary_mul,
  `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial.ordinary_pow,
  `OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.exists_avoiding_of_budget,
  `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.mean_energy_le,
  `OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral.bernoulli_mgf_le,
  `OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral.binomial_tail_le,
  `OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.exists_samples,
  `OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.sum_exp_le,
  `OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.sum_exp_samples_le,
  `OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.sum_potential_le,
  `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor.log2_value_append_true,
  `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor.value_append,
  `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor.value_eq_toNat,
  `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor.value_lt_two_pow_length,
  `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram.ofDigits_eq_value,
  `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram.value_append,
  `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat,
  `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.original_sat_main,
  `OAI.Algorithms.SubexponentialSAT.Subexp.TensorSpectrum.productKernel_inverse,
  `OAI.Algorithms.SubexponentialSAT.SubexpFactorProgram.toNat_append,
  `OAI.Algorithms.SubexponentialSAT.SubexpFactorProgram.toNat_lt_pow_length,
  `OAI.Algorithms.SubexponentialSAT.SubexpParameterProgram.log2_value_append_true,
  `OAI.Algorithms.SubexponentialSAT.SubexpParameterProgram.value_append,
  `OAI.Algorithms.SubexponentialSAT.SubexpParameterProgram.value_eq_toNat,
  `OAI.Algorithms.SubexponentialSAT.SubexpParameterProgram.value_lt_two_pow_length,
  `OAI.Algorithms.SubexponentialSAT.SubexpSeparation.sum_prod_eq_prod_sum,
  `OAI.Algorithms.SubexponentialSAT.SubexpSwapMultiplicity.card_negative,
  `OAI.Algorithms.SubexponentialSAT.SubexpSwapMultiplicity.card_negative_eq_sum,
  `OAI.Algorithms.SubexponentialSAT.SubexpSwapMultiplicity.card_positive,
  `OAI.Algorithms.SubexponentialSAT.SubexpSwapMultiplicity.card_positive_eq_sum,
  `OAI.Algorithms.SubexponentialSAT.SubexpSwapMultiplicity.two_mul_card_negative,
  `OAI.Algorithms.SubexponentialSAT.SubexpSwapMultiplicity.two_mul_card_positive,
  `OAI.Algorithms.SubexponentialSAT.TypeDistribution.mean_restrict,
  `OAI.Algorithms.SubexponentialSAT.TypeDistribution.squared_deviation_eq_collisions,
  `OAI.Algorithms.SubexponentialSAT.TypeDistribution.sum_fiberCount_sq,
  `OAI.Bridges.AnthropicETH.not_positiveRateETH_implies_ethIsFalse,
  `OAI.Bridges.ETH.foldr_max_le,
  `OAI.Bridges.ETH.le_foldr_max,
  `OAI.Bridges.ETH.not_positiveRateETH,
  `OAI.ParityWL.Complexity.decodeBits_bits,
  `OAI.ParityWL.Complexity.list_sum_map_le,
  `RecursionToBound.foldr_max_zero_le,
  dottedName "_private.Groundwork.Net.Colouring.0.Groundwork.Colouring.card_prescribed",
  dottedName "_private.Groundwork.Net.Colouring.0.Groundwork.Colouring.cheb_nat",
  dottedName "_private.Groundwork.Net.Colouring.0.Groundwork.Colouring.exists_colouring_core",
  dottedName "_private.Groundwork.Net.Colouring.0.Groundwork.Colouring.sum_Ys_sq",
  dottedName "_private.Groundwork.Net.Colouring.0.Groundwork.Colouring.sum_Zs_sq",
  dottedName "_private.StepMachines.Prog.NetRun.0.Groundwork.Prog.NetE.sum_map_le"]

def moduleNames : Array Name := #[
  `EthBridge.AnthropicChain, `EthBridge.OpenAIChain, `EthBridge.WordRAM]

def nameJson : Name → Json
  | .anonymous => .arr #[toJson "anonymous"]
  | .str parent component => .arr #[toJson "str", nameJson parent, toJson component]
  | .num parent component => .arr #[toJson "num", nameJson parent, toJson component]

def binderJson : BinderInfo → Json
  | .default => toJson "explicit"
  | .implicit => toJson "implicit"
  | .strictImplicit => toJson "strict_implicit"
  | .instImplicit => toJson "instance_implicit"

def levelJson (params : Std.HashMap Name Nat) : Level → Except String Json
  | .zero => return .arr #[toJson "zero"]
  | .succ l => do
    return .arr #[toJson "succ", ← levelJson params l]
  | .max l r => do
    return .arr #[toJson "max", ← levelJson params l, ← levelJson params r]
  | .imax l r => do
    return .arr #[toJson "imax", ← levelJson params l, ← levelJson params r]
  | .param name => do
    let some index := params[name]?
      | throw s!"Undeclared universe parameter: {name}"
    return .arr #[toJson "parameter", toJson index]
  | .mvar id => throw s!"Universe metavariable in compiled type: {id.name}"

def exprJson (params : Std.HashMap Name Nat) : Expr → Except String Json
  | .bvar index => return .arr #[toJson "bound_variable", toJson index]
  | .fvar id => throw s!"Free variable in compiled type: {id.name}"
  | .mvar id => throw s!"Expression metavariable in compiled type: {id.name}"
  | .sort level => do
    return .arr #[toJson "sort", ← levelJson params level]
  | .const name levels => do
    let encoded ← levels.toArray.mapM (levelJson params)
    return .arr #[toJson "constant", nameJson name, .arr encoded]
  | .app fn arg => do
    return .arr #[toJson "application", ← exprJson params fn, ← exprJson params arg]
  | .lam _ domain body binderInfo => do
    return .arr #[toJson "lambda", binderJson binderInfo,
      ← exprJson params domain, ← exprJson params body]
  | .forallE _ domain body binderInfo => do
    return .arr #[toJson "forall", binderJson binderInfo,
      ← exprJson params domain, ← exprJson params body]
  | .letE _ type value body nonDep => do
    return .arr #[toJson "let", toJson nonDep, ← exprJson params type,
      ← exprJson params value, ← exprJson params body]
  | .lit (.natVal value) => return .arr #[toJson "natural_literal", toJson value]
  | .lit (.strVal value) => return .arr #[toJson "string_literal", toJson value]
  | .mdata _ expression => exprJson params expression
  | .proj structureName fieldIndex expression => do
    return .arr #[toJson "projection", nameJson structureName, toJson fieldIndex,
      ← exprJson params expression]

def extract (env : Environment) (output : System.FilePath) : IO Unit := do
  let mut declarations : Array Json := #[]
  for name in theoremNames do
    let some info := env.find? name
      | throw <| IO.userError s!"Required declaration unavailable: {name}"
    match info with
    | .thmInfo _ => pure ()
    | _ => throw <| IO.userError s!"Expected theorem declaration: {name}"
    let mut params : Std.HashMap Name Nat := {}
    for index in [:info.levelParams.length] do
      let parameter := info.levelParams[index]!
      if params.contains parameter then
        throw <| IO.userError s!"Duplicate universe parameter in {name}: {parameter}"
      params := params.insert parameter index
    let expression ← match exprJson params info.type with
      | .ok result => pure result
      | .error message => throw <| IO.userError s!"{name}: {message}"
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => (env.header.moduleNames[idx.toNat]!).toString
      | none => "<unknown>"
    if moduleName == "<unknown>" then
      throw <| IO.userError s!"Required theorem has unknown source module: {name}"
    declarations := declarations.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson moduleName),
      ("kind", toJson "theorem"),
      ("original_universe_parameter_names", toJson <| info.levelParams.map Name.toString),
      ("normalized_type", Json.mkObj [
        ("universe_parameter_count", toJson info.levelParams.length),
        ("expression", expression)])]
    (← IO.getStderr).putStrLn s!"Extracted compiled type: {name}"
  let metadata := Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("lean_version", toJson Lean.versionString),
    ("import_level", toJson "private"),
    ("modules", toJson <| moduleNames.map Name.toString),
    ("theorems", toJson <| theoremNames.map Name.toString),
    ("declaration_count", toJson declarations.size),
    ("normalization", toJson <| #[
      "binder names omitted; binderInfo retained",
      "universe parameter names replaced by ordered declaration parameter indices",
      "Expr.mdata annotations erased",
      "all other expression/level constructors and data retained",
      "no unfolding, reduction, or pretty-printing"])]
  IO.FS.writeFile output <| (Json.mkObj [
    ("metadata", metadata), ("declarations", .arr declarations)]).compress
  (← IO.getStderr).putStrLn s!"Saved {declarations.size} normalized compiled theorem types."

end RefactorTypeAudit

def main (args : List String) : IO UInt32 := do
  if (← IO.getEnv "SSH_CONNECTION").isNone then
    throw <| IO.userError "Run this extractor only through SSH on the authorized remote machine."
  let [output] := args
    | throw <| IO.userError "Usage: lake env lean --run ExtractRefactorTypes.lean OUTPUT.json"
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules
    (RefactorTypeAudit.moduleNames.map fun moduleName => { module := moduleName })
    {} (level := .private)
  RefactorTypeAudit.extract (env.setExporting false) output
  return 0
