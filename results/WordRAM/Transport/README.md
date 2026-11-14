# Verified RAM-to-FinTM2 transport

The principal result is `RAMToTM.Transport.exists_tmW_of_exec_unconditional`.
For every word-RAM program `P` and width parameter `b`, there is a `FinTM2` machine with finite
stack alphabets and a polynomial bound `q * (t + |x| + 1)^q`. When `P` accepts/rejects on the
actual initial memory within `t` RAM steps, that machine returns the same one-bit verdict on the
exact bit-string input.

`RAMToTM.Transport.nonempty_isPolyT_machine` constructs the required actual `Nonempty`
`Groundwork.IsPolyT` instance from the machine's own functions `initSt`, `stepSt` and `outSt`.
It is not a hypothesis, and the three exhibited fragment theorems expose actual `PolyT` costs.
Other important input is the independently checked interpreter, execution relation, finite
state-size bound and host composition, whose paths are listed in the verification records.

* Sources: `RAMToTM/Transport/{InitPoly,InitPrims,StepPoly,Closure}.lean`.
* Reproduce: `./results/verify_wordram_closure.sh` (about 75 seconds in the last full rebuild).
* Audit: `ClosureAxioms.txt`, `ClosureSignatures.txt`. All 16 exported results use only
  `propext`, `Classical.choice`, and `Quot.sound`; `wsOf_eq_ramInput` uses only `propext`.
* Provenance: sources are unchanged from `.ultramath/smwgnm7hp/m2/src/RAMToTM/Transport`.
  Verification reuses frozen `ToTuring` modules through the upstream verified build of that
  closure: `.ultramath/smwgnm7hp/m2/build`. It does not run the entire 810-file ETH rebuild.
  Frozen statement SHA256 remains `47f78a9550d95b37d8718dd1ee16ae824da893a5e17c319f737e6d0a5ed24944`.

Scope: this completes the *machine transport* between the pinned Prove2Me model and `FinTM2`.
It does not establish existence of a subexponential 3-SAT algorithm, does not salvage an invalid
zero-variable bit-word encoding, and is not by itself an ordinary word-RAM refutation of ETH.
The OpenAI route's constructive algorithm/runtime implementation remains incomplete as before.
