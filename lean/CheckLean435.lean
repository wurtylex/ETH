import EthBridge.OpenAIChain
import EthBridge.AnthropicChain
import EthBridge.Elementary.Crossing
import EthBridge.Elementary.DecisionBridge
import EthBridge.Elementary.PieceBounds
import EthBridge.Elementary.WideCut
import EthBridge.Elementary.Pieces
import EthBridge.Elementary.PiecesBounds
import EthBridge.Elementary.PiecesSpec
import EthBridge.Elementary.ReusedRecursion

#print axioms EthBridge.OpenAIChain.not_eth
#print axioms EthBridge.AnthropicChain.not_eth
#print axioms EthBridge.Elementary.ReusedRecursion.not_eth
#print axioms EthBridge.Elementary.Crossing.mem_lowIndices
#print axioms EthBridge.Elementary.Crossing.mem_highIndices
#print axioms EthBridge.Elementary.Crossing.pieceA_add_pieceB
#print axioms EthBridge.Elementary.Crossing.indexed_rows
#print axioms EthBridge.Elementary.Crossing.indexed_cols
#print axioms EthBridge.Elementary.Crossing.collect_rows
#print axioms EthBridge.Elementary.Crossing.collect_cols
#print axioms EthBridge.Elementary.Crossing.rowCoeff_low_eq_zero
#print axioms EthBridge.Elementary.Crossing.colCoeff_high_eq_zero
#print axioms EthBridge.Elementary.Crossing.pieceA_rows
#print axioms EthBridge.Elementary.Crossing.pieceA_cols
#print axioms EthBridge.Elementary.Crossing.pieceB_rows
#print axioms EthBridge.Elementary.Crossing.pieceB_cols
#print axioms EthBridge.Elementary.Crossing.size_three_pow_add_three_le
#print axioms EthBridge.Elementary.Crossing.capW_half_add_six_le
#print axioms EthBridge.Elementary.Crossing.capW_half_le_nameWidth
#print axioms EthBridge.Elementary.Crossing.nameWidth_le_two_mul
#print axioms EthBridge.Elementary.Crossing.capW_half_le_two_mul
#print axioms EthBridge.Elementary.Crossing.card_sparseLab_half_le
#print axioms EthBridge.Elementary.Crossing.pieceA_rows_words
#print axioms EthBridge.Elementary.Crossing.pieceB_cols_words
#print axioms EthBridge.Elementary.PieceBounds.abs_sum_le_double_bits
#print axioms EthBridge.Elementary.PieceBounds.abs_rowCoeff_le
#print axioms EthBridge.Elementary.PieceBounds.abs_colCoeff_le
#print axioms EthBridge.Elementary.PieceBounds.lowIndices_card_le
#print axioms EthBridge.Elementary.PieceBounds.highIndices_card_le
#print axioms EthBridge.Elementary.PieceBounds.abs_pieceA_le
#print axioms EthBridge.Elementary.PieceBounds.abs_pieceB_le
#print axioms EthBridge.Elementary.PieceBounds.favorable_cap_sum_le
#print axioms EthBridge.Elementary.PieceBounds.favorable_cap_sum_le_log
#print axioms EthBridge.Elementary.PieceBounds.par_of_two_piece_data
#print axioms EthBridge.Elementary.WideCut.full_input_identity
#print axioms EthBridge.Elementary.Pieces.sparseTop_polyT
#print axioms EthBridge.Elementary.Pieces.collectBot_polyT
#print axioms EthBridge.Elementary.Pieces.sparseBot_polyT
#print axioms EthBridge.Elementary.Pieces.botF_common
#print axioms EthBridge.Elementary.Pieces.bitsOf_ofFn
#print axioms EthBridge.Elementary.Pieces.collectBot_low
#print axioms EthBridge.Elementary.Pieces.collectBot_high
#print axioms EthBridge.Elementary.Pieces.sparseTop_eq
#print axioms EthBridge.Elementary.Pieces.pieceA_rows_program
#print axioms EthBridge.Elementary.Pieces.pieceB_cols_program
#print axioms EthBridge.Elementary.Pieces.sparseValue_polyT
#print axioms EthBridge.Elementary.Pieces.sparseValue_eq_sum
#print axioms EthBridge.Elementary.Pieces.value_polyT
#print axioms EthBridge.Elementary.Pieces.value_low
#print axioms EthBridge.Elementary.Pieces.value_high
#print axioms EthBridge.Elementary.Pieces.wideTop_polyT
#print axioms EthBridge.Elementary.Pieces.wideBot_polyT
#print axioms EthBridge.Elementary.Pieces.pieceA_cols_program
#print axioms EthBridge.Elementary.Pieces.pieceB_rows_program
#print axioms EthBridge.Elementary.Pieces.family_keeps
#print axioms EthBridge.Elementary.PiecesBounds.sparseTop_bound
#print axioms EthBridge.Elementary.PiecesBounds.collectBot_bound
#print axioms EthBridge.Elementary.PiecesBounds.sparseBot_bound
#print axioms EthBridge.Elementary.PiecesBounds.ofFn_bitsOf
#print axioms EthBridge.Elementary.PiecesBounds.value_bound
#print axioms EthBridge.Elementary.PiecesBounds.wideTop_bound
#print axioms EthBridge.Elementary.PiecesBounds.wideBot_bound
#print axioms EthBridge.Elementary.PiecesBounds.family_bounds
#print axioms EthBridge.Elementary.PiecesSpec.family_spec
#print axioms EthBridge.Elementary.PiecesSpec.family_par
#print axioms EthBridge.Elementary.DecisionBridge.rate_tendsto_zero
#print axioms EthBridge.Elementary.DecisionBridge.exponential_below
#print axioms EthBridge.Elementary.DecisionBridge.count_bound_below
#print axioms EthBridge.Elementary.DecisionBridge.wrapped_time_below
#print axioms EthBridge.Elementary.DecisionBridge.subexp_of_count_rate
#print axioms EthBridge.Elementary.DecisionBridge.subexp_of_countInRateN
#print axioms EthBridge.Elementary.DecisionBridge.not_eth_of_countInRateN
#print axioms EthBridge.Elementary.DecisionBridge.not_eth_of_pieces
#print axioms EthBridge.Elementary.ReusedRecursion.not_eth_tm

example : ¬ ComplexityAbstracts.SubexponentialSATAbstract.ETH := EthBridge.OpenAIChain.not_eth
example : ¬ ComplexityAbstracts.SubexponentialSATAbstract.ETH := EthBridge.AnthropicChain.not_eth
example : ¬ ComplexityAbstracts.SubexponentialSATAbstract.ETH := EthBridge.Elementary.ReusedRecursion.not_eth
