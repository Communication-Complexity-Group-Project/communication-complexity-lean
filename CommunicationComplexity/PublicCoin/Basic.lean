import CommunicationComplexity.CoinTape
import CommunicationComplexity.Deterministic.Basic
import Mathlib.Data.Real.Basic

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

namespace PublicCoin

/-- A public-coin protocol is a deterministic protocol where both
Alice and Bob see shared randomness `Ω`. Alice's input is `(ω, x)`
and Bob's is `(ω, y)`. -/
abbrev Protocol (Ω : Type*) (X Y α : Type*) :=
  Deterministic.Protocol (Ω × X) (Ω × Y) α

namespace Protocol

variable {Ω : Type*} {X Y α : Type*}

/-- Execute a public-coin protocol on inputs `x`, `y` with
shared randomness `ω`. -/
def rrun (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) : α :=
  p.run (ω, x) (ω, y)

@[simp]
theorem rrun_eq (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) :
    p.rrun x y ω = p.run (ω, x) (ω, y) := rfl

/-- A public-coin protocol `ε`-satisfies a predicate `Q` if for every
input `(x, y)`, the probability that `Q x y (p.rrun ...)` fails
is at most `ε`. -/
def ApproxSatisfies
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (Q : X → Y → α → Prop)
    (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω |
      ¬Q x y (p.rrun x y ω)}).toReal ≤ ε

/-- A public-coin protocol `ε`-computes a function `f` if for every
input `(x, y)`, the probability (under the shared coin-flip measure)
of producing an incorrect answer is at most `ε`. -/
noncomputable def ApproxComputes
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω |
      p.rrun x y ω ≠ f x y}).toReal ≤ ε

theorem ApproxComputes_eq_ApproxSatisfies
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) :
    p.ApproxComputes f ε =
      p.ApproxSatisfies (fun x y a => a = f x y) ε := by
  simp only [ApproxComputes, ApproxSatisfies, ne_eq]

end Protocol

end PublicCoin

end CommunicationComplexity
