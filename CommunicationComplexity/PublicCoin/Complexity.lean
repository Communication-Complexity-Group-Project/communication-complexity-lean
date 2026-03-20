import CommunicationComplexity.Deterministic.Complexity
import CommunicationComplexity.PublicCoin.Basic
import CommunicationComplexity.PublicCoin.FiniteMessage

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

namespace PublicCoin

/-- The `ε`-error public-coin randomized communication complexity of `f`,
defined as the minimum worst-case number of bits exchanged over all
public-coin randomized protocols that compute `f` with error at most
`ε` on every input. -/
noncomputable def communicationComplexity
    {X Y α} (f : X → Y → α) (ε : ℝ) : ENat :=
  ⨅ (n : ℕ)
    (p : Protocol (CoinTape n) X Y α)
    (_ : p.ApproxComputes f ε),
    (p.complexity : ENat)

theorem communicationComplexity_le_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    communicationComplexity f ε ≤ m ↔
      ∃ (n : ℕ) (p : Protocol (CoinTape n) X Y α),
        p.ApproxComputes f ε ∧
        p.complexity ≤ m := by
  unfold communicationComplexity
  simp only [Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]

theorem le_communicationComplexity_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    (m : ENat) ≤ communicationComplexity f ε ↔
      ∀ (n : ℕ) (p : Protocol (CoinTape n) X Y α),
        p.ApproxComputes f ε →
        m ≤ p.complexity := by
  unfold communicationComplexity
  simp only [le_iInf_iff, Nat.cast_le]

theorem communicationComplexity_le_iff_finiteMessage
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    communicationComplexity f ε ≤ m ↔
      ∃ (n : ℕ)
        (p : FiniteMessage.Protocol (CoinTape n) X Y α),
        p.ApproxComputes f ε ∧
        p.complexity ≤ m := by
  rw [communicationComplexity_le_iff]
  constructor
  · -- Binary → FiniteMessage via ofProtocol
    rintro ⟨n, p, hp, hc⟩
    refine ⟨n, FiniteMessage.Protocol.ofProtocol p, ?_,
      Deterministic.FiniteMessage.Protocol.ofProtocol_complexity p ▸ hc⟩
    intro x y
    simp only [FiniteMessage.Protocol.rrun,
      Deterministic.FiniteMessage.Protocol.ofProtocol_run]
    exact hp x y
  · -- FiniteMessage → Binary via toProtocol
    rintro ⟨n, p, hp, hc⟩
    refine ⟨n, p.toProtocol, ?_,
      Deterministic.FiniteMessage.Protocol.toProtocol_complexity p ▸ hc⟩
    intro x y
    change (volume {ω : CoinTape n |
      Deterministic.Protocol.run (Deterministic.FiniteMessage.Protocol.toProtocol p)
        (ω, x) (ω, y) ≠ f x y}).toReal ≤ ε
    simp only [Deterministic.FiniteMessage.Protocol.toProtocol_run]
    exact hp x y

/-- Communication complexity is monotone in ε: allowing more error can
only make computation easier. -/
theorem communicationComplexity_mono
    {X Y α} (f : X → Y → α) {ε ε' : ℝ} (h : ε' ≤ ε) :
    communicationComplexity f ε ≤ communicationComplexity f ε' := by
  match hm : communicationComplexity f ε' with
  | ⊤ => exact le_top
  | (m : ℕ) =>
    obtain ⟨n, p, hp, hc⟩ :=
      (communicationComplexity_le_iff f ε' m).mp (le_of_eq hm)
    exact (communicationComplexity_le_iff f ε m).mpr
      ⟨n, p, fun x y => le_trans (hp x y) h, hc⟩

end PublicCoin

end CommunicationComplexity
