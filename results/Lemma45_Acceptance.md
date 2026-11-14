# Independent verification: OpenAI Lemma 4.5 schedule and placement

## Provenance

The `smwg8h0gx` swarm ended with seven accepted packages but the schedule direction marked
**abandoned**: the member stopped before submitting a report. This is not a retroactive swarm
acceptance. The surviving code at `.ultramath/smwg8h0gx/m8/lean/L45/` was independently read,
rebuilt and audited after that abandonment.

## What is actually verified

Two declarations in `L45/Placement.lean`'s dependency tree are the endpoint:

- `L45.exists_schedule` produces schedules whose empty-scope factors use group 1, whose
  label multiplicities satisfy `card(label class) * D ≤ 2M`, and whose variable groups satisfy
  `card(group) * r ≤ 2n`, in the paper's hypotheses `2(b+w)D² ≤ M` and `2Qr² ≤ n`, where
  `D = r^(2Q)` and `M` counts incidences.
- `L45.lemma45_placement` additionally places incidences injectively into `⌊2M/D⌋` copies,
  by applying the already accepted `OpenAI4.MultiCopy.exists_placement` to those label bounds.

The proof computes label/group second moments by finite product-space counting. It splits
independent label pairs from pairs sharing a factor or variable, bounds the latter by `M(b+w)`,
then averages the sum of two normalized nonnegative centered-square functionals. It is a finite
existence proof, not a probabilistic hypothesis. It also performs explicit uniform counting for
the group deviations rather than asserting independence as an axiom.

## Checks run

```sh
./results/verify_lemma45.sh
```

This runs the source's `./build.sh --axioms` in its own directory, rebuilding
Basic/Card/Count/Labels/Dep/Moments/Main/Schedule/Exists/Lemma45/Placement. All these modules
compiled with the accepted MultiCopy and Eth4 modules read-only. The 11 axiom reports for
`sum_factor`, `card_prob`, `card_prob_transport`, `card_agree_fun`, `card_agree_time`,
`sum_dep_le`, `sum_sq_cnt`, `sum_sq_cnt_le`, `sum_Xi_le`, `exists_schedule` and
`lemma45_placement` each contain only `propext`, `Classical.choice` and `Quot.sound`.

A source scan found no `sorry`, `admit`, `native_decide` or custom axiom. The warnings are
unused-variable and deprecation/style warnings, not proof holes.

## Scope: existence, not implementation or full Design

This verifies finite label *existence*, not a conditional-expectation machine algorithm, its
iteration count or its bit complexity.

**Integration update:** the common interface was subsequently constructed and independently
rebuilt in `.ultramath/smwgaim18/m1/IncBridge.lean`. It transports incidence/cardinality/label
and placement data without identifying the two underlying types by hand. The completed paper
statement (including the interval-tail hypothesis (4.8)) is in
`.ultramath/smwgaim18/m1/Lemma47.lean`. The older `EthIntegrated.Lemma47` omits that hypothesis;
it is not claimed to follow from this construction. The standalone salvage verification below is
a record of the abandoned member's status at review time, not a claim that integration was absent.

This does not prove the asymptotic exponent balance (4.18), the complete Tanner shortening,
Appendix A's priority/normalization argument, the sparse-algorithm IAM/bit costs, or
`MainResults.ETHIsFalse` beyond the already established Anthropic-model proof. The unchanged
caveat about ordinary word-RAM/encoding translation applies.
