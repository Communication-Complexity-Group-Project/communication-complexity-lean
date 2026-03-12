import Mathlib
import CommunicationComplexity.Det.Basic
import CommunicationComplexity.Det.Generalized
import CommunicationComplexity.Rand.Basic

open MeasureTheory

@[simp]
private theorem WithTop.iInf_le_coe_iff {ι : Sort*} {f : ι → WithTop ℕ} {n : ℕ} :
    iInf f ≤ ↑n ↔ ∃ i, f i ≤ ↑n := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    apply not_lt.mpr h
    have : ∀ i, (↑(n + 1) : WithTop ℕ) ≤ f i := fun i => by
      match f i, hne i with
      | none, _ => exact le_top
      | some m, hi => exact WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp hi))
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)) (le_iInf this)
  · rintro ⟨i, hi⟩
    exact (iInf_le f i).trans hi

noncomputable def deterministic_communication_complexity {X Y α} (f : X → Y → α) : WithTop ℕ :=
  ⨅ (p : DetProtocol X Y α) (_ : p.computes f), (p.complexity : WithTop ℕ)

theorem det_cc_le_iff {X Y α} (f : X → Y → α) (n : ℕ) :
    deterministic_communication_complexity f ≤ n ↔
      ∃ p : DetProtocol X Y α, p.computes f ∧ p.complexity ≤ n := by
  simp [deterministic_communication_complexity]

theorem le_det_cc_iff {X Y α} (f : X → Y → α) (n : ℕ) :
    (n : WithTop ℕ) ≤ deterministic_communication_complexity f ↔
      ∀ p : DetProtocol X Y α, p.computes f → n ≤ p.complexity := by
  simp only [deterministic_communication_complexity, le_iInf_iff]
  constructor
  · intro h p hp; exact_mod_cast h p hp
  · intro h p hp; exact_mod_cast h p hp

noncomputable def randomized_communication_complexity.{u₁, u₂} {X Y α} (f : X → Y → α) (ε : ℝ) : WithTop ℕ :=
  ⨅ (Ω_X : Type u₁) (Ω_Y : Type u₂) (_ : MeasureSpace Ω_X) (_ : MeasureSpace Ω_Y)
    (_ : IsProbabilityMeasure (volume : Measure Ω_X))
    (_ : IsProbabilityMeasure (volume : Measure Ω_Y))
    (p : RandProtocol Ω_X Ω_Y X Y α) (_ : p.approx_computes f ε),
    (p.complexity : WithTop ℕ)

theorem rand_cc_le_iff.{u₁, u₂} {X Y α} (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    randomized_communication_complexity.{u₁, u₂} f ε ≤ n ↔
      ∃ (Ω_X : Type u₁) (Ω_Y : Type u₂) (_ : MeasureSpace Ω_X) (_ : MeasureSpace Ω_Y)
        (_ : IsProbabilityMeasure (volume : Measure Ω_X))
        (_ : IsProbabilityMeasure (volume : Measure Ω_Y))
        (p : RandProtocol Ω_X Ω_Y X Y α),
        p.approx_computes f ε ∧ p.complexity ≤ n := by
  simp [randomized_communication_complexity]

theorem le_rand_cc_iff.{u₁, u₂} {X Y α} (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    (n : WithTop ℕ) ≤ randomized_communication_complexity.{u₁, u₂} f ε ↔
      ∀ (Ω_X : Type u₁) (Ω_Y : Type u₂) [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
        [IsProbabilityMeasure (volume : Measure Ω_X)]
        [IsProbabilityMeasure (volume : Measure Ω_Y)]
        (p : RandProtocol Ω_X Ω_Y X Y α),
        p.approx_computes f ε → n ≤ p.complexity := by
  unfold randomized_communication_complexity
  constructor
  · intro h Ω_X Ω_Y msX msY ipX ipY p hp
    have := h.trans (iInf_le_of_le Ω_X (iInf_le_of_le Ω_Y (iInf_le_of_le msX (iInf_le_of_le msY
      (iInf_le_of_le ipX (iInf_le_of_le ipY (iInf_le_of_le p (iInf_le_of_le hp le_rfl))))))))
    exact_mod_cast this
  · intro h
    apply le_iInf; intro Ω_X; apply le_iInf; intro Ω_Y
    apply le_iInf; intro msX; apply le_iInf; intro msY
    apply le_iInf; intro ipX; apply le_iInf; intro ipY
    apply le_iInf; intro p; apply le_iInf; intro hp
    exact_mod_cast @h Ω_X Ω_Y msX msY ipX ipY p hp
