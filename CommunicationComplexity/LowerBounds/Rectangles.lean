import CommunicationComplexity.Rectangles.Basic

namespace DetProtocol

variable {X Y α : Type*}

/-- Rephrasing of `rectangle_partition` using non-explicit partitions.
If `deterministic_communication_complexity g ≤ n`, then there is a monochromatic
rectangle partition of `X × Y` with at most `2^n` rectangles. -/
theorem mono_rectangle_partition_of_det_cc
    (g : X → Y → α) (n : ℕ)
    (h : deterministic_communication_complexity g ≤ n) :
    ∃ Part : Set (Set (X × Y)),
      isMonoRectPartition Part g ∧
      Set.ncard Part ≤ 2 ^ n := by
  obtain ⟨p, hp, hc⟩ := (det_cc_le_iff g n).mp h
  exact ⟨leafRectangles p,
    leafRectangles_isMonoRectPartition p g hp,
    (leafRectangles_card p).trans
      (Nat.pow_le_pow_right (by omega) hc)⟩

/-- Rectangle lower-bound method: to prove `CC(g) ≥ n + 1`, it suffices to show
every monochromatic rectangle partition of `g` has more than `2^n` parts. -/
theorem det_cc_lower_bound
    (g : X → Y → α) (n : ℕ)
    (h : ∀ Part : Set (Set (X × Y)),
      isMonoRectPartition Part g →
      2 ^ n < Set.ncard Part) :
    (n + 1 : ℕ) ≤ deterministic_communication_complexity g := by
  rw [le_det_cc_iff]
  intro p hp
  have hle : deterministic_communication_complexity g ≤
      p.complexity :=
    (det_cc_le_iff g p.complexity).mpr ⟨p, hp, le_refl _⟩
  obtain ⟨Part, hPart, hCard⟩ :=
    mono_rectangle_partition_of_det_cc g p.complexity hle
  have hsuff := h Part hPart
  by_contra hlt; push_neg at hlt
  have : 2 ^ p.complexity ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

end DetProtocol
