import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Real.Basic
import CommunicationComplexity.Basic
import CommunicationComplexity.LowerBounds.Rectangles

open Classical in
/-- The real-valued matrix of a Boolean function `f : X → Y → Bool`,
where the `(x, y)` entry is `1` if `f x y = true` and `0` otherwise. -/
noncomputable def boolFunctionMatrix {X Y : Type*}
    (f : X → Y → Bool) : Matrix X Y ℝ :=
  Matrix.of fun x y => if f x y then 1 else 0

/-- The rank of a Boolean function `f`, defined as the rank of its
real-valued matrix over `ℝ`. -/
noncomputable def boolFunctionRank {X Y : Type*} [Fintype Y]
    (f : X → Y → Bool) : ℕ :=
  (boolFunctionMatrix f).rank

open Classical in
/-- The {0,1}-matrix of a subset `R ⊆ X × Y`. -/
noncomputable def rectMatrix {X Y : Type*}
    (R : Set (X × Y)) : Matrix X Y ℝ :=
  Matrix.of fun x y => if (x, y) ∈ R then 1 else 0

/-- For a rectangle `R = A ×ˢ B`, the matrix `rectMatrix R` is the
outer product of indicator vectors, hence has rank ≤ 1. -/
theorem rank_rectMatrix_le_one {X Y : Type*}
    [Fintype Y]
    (R : Set (X × Y)) (hR : DetProtocol.isRectangle R) :
    (rectMatrix R).rank ≤ 1 := by
  classical
  -- R = A ×ˢ B for some A, B
  obtain ⟨A, B, rfl⟩ := hR
  -- rectMatrix (A ×ˢ B) = vecMulVec (indA) (indB)
  have heq : rectMatrix (A ×ˢ B) =
      Matrix.vecMulVec
        (fun x => if x ∈ A then (1 : ℝ) else 0)
        (fun y => if y ∈ B then (1 : ℝ) else 0) := by
    ext x y
    simp only [rectMatrix, Matrix.of_apply,
      Matrix.vecMulVec, Set.mem_prod_eq]
    cases Classical.em (x ∈ A) <;>
      cases Classical.em (y ∈ B) <;> simp_all
  rw [heq]; exact Matrix.rank_vecMulVec_le _ _

/-- Matrix rank is subadditive: `rank (A + B) ≤ rank A + rank B`. -/
theorem Matrix.rank_add_le {X Y : Type*}
    [Fintype Y]
    (A B : Matrix X Y ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  -- rank = finrank of range of mulVecLin
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  -- range (f + g) ≤ range f ⊔ range g
  have hle : LinearMap.range (A.mulVecLin + B.mulVecLin) ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    intro v hv
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hv
    simp only [LinearMap.add_apply]
    exact Submodule.add_mem_sup
      (LinearMap.mem_range.mpr ⟨w, rfl⟩)
      (LinearMap.mem_range.mpr ⟨w, rfl⟩)
  exact (Submodule.finrank_mono hle).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- Matrix rank is subadditive over finite sums:
`rank (∑ i in s, A i) ≤ ∑ i in s, rank (A i)`. -/
theorem Matrix.rank_sum_le {X Y : Type*}
    [Fintype Y]
    {ι : Type*} (s : Finset ι)
    (A : ι → Matrix X Y ℝ) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction with
  | empty => simp [Matrix.rank_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (Matrix.rank_add_le _ _).trans (Nat.add_le_add_left ih _)

open DetProtocol in
/-- The rank of a Boolean function is at most the number of
rectangles in any monochromatic rectangle partition.
Each true-mono rectangle contributes a rank-1 matrix,
M_f is their sum, and rank is subadditive. -/
theorem boolFunctionRank_le_ncard
    {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool)
    (Part : Set (Set (X × Y)))
    (hPart : isMonoRectPartition Part f) :
    boolFunctionRank f ≤ Set.ncard Part := by
  classical
  let PF := (Set.toFinite Part).toFinset
  -- True-mono rectangles: those where every point has f = true
  let trueRects := PF.filter (fun R =>
    ∃ p ∈ R, f p.1 p.2 = true)
  -- Step 1: boolFunctionMatrix f = ∑ R in trueRects, rectMatrix R
  have hsum : boolFunctionMatrix f =
      ∑ R ∈ trueRects, rectMatrix R := by
    ext x y
    simp only [boolFunctionMatrix, rectMatrix, Matrix.of_apply,
      Matrix.sum_apply]
    -- (x,y) is in exactly one rectangle R₀
    obtain ⟨R₀, hR₀_mem, hR₀_in⟩ := hPart.exists_mem (x, y)
    -- For any R ≠ R₀ in Part, (x,y) ∉ R by disjointness
    have hother : ∀ R ∈ PF, R ≠ R₀ →
        (x, y) ∉ R := by
      intro R hR hne hmem
      exact hne (hPart.eq_of_mem
        ((Set.toFinite Part).mem_toFinset.mp hR)
        hR₀_mem hmem hR₀_in)
    -- Therefore the sum has at most one nonzero term
    cases hf : f x y
    · -- f x y = false: boolFunctionMatrix entry is 0
      -- R₀ is false-mono, so R₀ ∉ trueRects
      -- No other R contains (x,y), so all terms are 0
      simp only [Bool.false_eq_true, ↓reduceIte]
      symm; apply Finset.sum_eq_zero
      intro R hR
      by_cases hne : R = R₀
      · -- R = R₀ is false-mono but R ∈ trueRects — contradiction
        subst hne
        obtain ⟨⟨x', y'⟩, hpin, hftrue⟩ :=
          (Finset.mem_filter.mp hR).2
        have hmono := hPart.apply_eq hR₀_mem hR₀_in hpin
        rw [hf] at hmono; simp [← hmono] at hftrue
      · simp [hother R (Finset.mem_filter.mp hR).1 hne]
    · -- f x y = true: boolFunctionMatrix entry is 1
      simp only [↓reduceIte]
      -- R₀ ∈ trueRects
      have hR₀_true : R₀ ∈ trueRects :=
        Finset.mem_filter.mpr
          ⟨(Set.toFinite Part).mem_toFinset.mpr hR₀_mem,
           ⟨x, y⟩, hR₀_in, hf⟩
      symm
      rw [Finset.sum_eq_single R₀
        (fun R hR hne => by
          simp [hother R (Finset.mem_filter.mp hR).1 hne])
        (fun h => absurd hR₀_true h)]
      simp [hR₀_in]
  -- Step 2: rank ≤ ∑ rank ≤ |trueRects| ≤ |Part|
  calc boolFunctionRank f
      = (∑ R ∈ trueRects, rectMatrix R).rank := by
        unfold boolFunctionRank; rw [← hsum]
    _ ≤ ∑ R ∈ trueRects, (rectMatrix R).rank :=
        Matrix.rank_sum_le _ _
    _ ≤ ∑ _R ∈ trueRects, 1 :=
        Finset.sum_le_sum (fun R hR => by
          have hRP := (Set.toFinite Part).mem_toFinset.mp
            (Finset.mem_filter.mp hR).1
          exact rank_rectMatrix_le_one R (hPart.1 R hRP))
    _ = trueRects.card := by simp
    _ ≤ PF.card := Finset.card_filter_le _ _
    _ = Set.ncard Part :=
        (Set.ncard_eq_toFinset_card Part (Set.toFinite Part)).symm

open DetProtocol in
/-- If the deterministic CC of `f` is at most `n`, then the rank
of `f` is at most `2^n`. -/
theorem boolFunctionRank_le_pow_of_det_cc
    {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (n : ℕ)
    (h : deterministic_communication_complexity f ≤ n) :
    boolFunctionRank f ≤ 2 ^ n := by
  obtain ⟨Part, hPart, hCard⟩ :=
    mono_rectangle_partition_of_det_cc f n h
  exact (boolFunctionRank_le_ncard f Part hPart).trans hCard

/-- Log-rank lower bound: the deterministic communication
complexity of a Boolean function `f` is at least `⌈log₂(rank f)⌉`.
-/
theorem log_rank_lower_bound
    {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) :
    (Nat.clog 2 (boolFunctionRank f) : WithTop ℕ) ≤
      deterministic_communication_complexity f := by
  -- Case split on whether CC is ⊤ or finite
  match h : deterministic_communication_complexity f with
  | ⊤ => exact le_top
  | (n : ℕ) =>
    exact_mod_cast Nat.clog_le_of_le_pow
      (boolFunctionRank_le_pow_of_det_cc f n (le_of_eq h))
