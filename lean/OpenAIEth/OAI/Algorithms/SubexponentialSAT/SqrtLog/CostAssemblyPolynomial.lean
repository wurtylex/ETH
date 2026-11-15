import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyMoment

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

/-- A closure predicate used only to certify that the displayed envelope is
a fixed polynomial, independently of the runtime model. -/
def Ordinary (f : ℕ → ℕ) : Prop := ∃ C d : ℕ, ∀ S, f S ≤ C*(S+1)^d

theorem ordinary_const (a : ℕ) : Ordinary (fun _ => a) := by
  exact ⟨a,0,by simp⟩

theorem ordinary_id : Ordinary (fun S => S) := by
  exact ⟨1,1,by intro S; simp⟩

theorem ordinary_add {f g : ℕ → ℕ} (hf : Ordinary f) (hg : Ordinary g) :
    Ordinary (fun S => f S+g S) :=
  Cslib.polynomiallyBounded_iff_le.mp ((Cslib.polynomiallyBounded_iff_le.mpr hf).add (Cslib.polynomiallyBounded_iff_le.mpr hg))

theorem ordinary_mul {f g : ℕ → ℕ} (hf : Ordinary f) (hg : Ordinary g) :
    Ordinary (fun S => f S*g S) :=
  Cslib.polynomiallyBounded_iff_le.mp ((Cslib.polynomiallyBounded_iff_le.mpr hf).mul (Cslib.polynomiallyBounded_iff_le.mpr hg))

theorem ordinary_pow {f : ℕ → ℕ} (hf : Ordinary f) (e : ℕ) :
    Ordinary (fun S => (f S)^e) :=
  Cslib.polynomiallyBounded_iff_le.mp ((Cslib.polynomiallyBounded_iff_le.mpr hf).pow e)

end SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

end OAI.Algorithms
