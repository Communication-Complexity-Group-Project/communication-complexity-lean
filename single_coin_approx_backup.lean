-- Backup of single_coin_approx proof (work in progress, has sorry's)
-- From CommunicationComplexity/PrivateCoin/GeneralFiniteMessage.lean lines 249-532

private theorem single_coin_approx
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasureSpace Ω] [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (φ : CoinTape n → Ω),
      ∀ (S : Set Ω),
        (volume (φ ⁻¹' S : Set (CoinTape n))).toReal ≤
        (volume S).toReal + δ := by
  classical
  -- Choose n large enough that (Fintype.card Ω) / 2^n < δ
  set k := Fintype.card Ω with hk_def
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (div_pos hδ hk_pos) (by norm_num : (1 : ℝ) / 2 < 1)
  -- hn : (1/2)^n < δ / k, which means k / 2^n < δ
  have hk_2n : (k : ℝ) / 2 ^ n < δ := by
    have h1 : (1 / 2 : ℝ) ^ n * k < δ := by
      calc (1 / 2 : ℝ) ^ n * k
          < δ / k * k := mul_lt_mul_of_pos_right hn hk_pos
        _ = δ := div_mul_cancel₀ δ (ne_of_gt hk_pos)
    have h2 : (k : ℝ) / 2 ^ n = (1 / 2) ^ n * k := by
      rw [one_div, inv_pow, div_eq_inv_mul]
    linarith
  -- Combinatorial construction: φ with each fiber of size
  -- ≤ volume({a}) * 2^n + 1
  have key : ∃ (φ : CoinTape n → Ω), ∀ (a : Ω),
      (((Finset.univ.filter
        (fun ω : CoinTape n => φ ω = a)).card : ℝ) ≤
        (volume ({a} : Set Ω)).toReal *
          (Fintype.card (CoinTape n) : ℝ) + 1) := by
    -- We construct φ by partitioning [0, N) into intervals, one per element of Ω.
    -- Each element a gets ⌊volume({a}).toReal * N⌋₊ or one more coin tapes.
    set N := Fintype.card (CoinTape n) with hN_def
    -- Order elements of Ω and CoinTape n via equivFin
    set e := Fintype.equivFin Ω with he_def
    set eN := Fintype.equivFin (CoinTape n) with heN_def
    -- Weight assigned to each element (floor of its fair share)
    set wt : Fin k → ℕ := fun j => ⌊(volume ({e.symm j} : Set Ω)).toReal * N⌋₊
    -- Σ vol({a_j}) = 1
    have hsum_vol : Finset.univ.sum (fun j : Fin k =>
        (volume ({e.symm j} : Set Ω)).toReal) = 1 := by
      -- Reindex from Fin k to Ω
      conv_lhs => rw [show Finset.univ.sum (fun j : Fin k =>
          (volume ({e.symm j} : Set Ω)).toReal) =
        Finset.univ.sum (fun a : Ω =>
          (volume ({a} : Set Ω)).toReal) from by
        rw [← Equiv.sum_comp e.symm]]
      -- Σ_a vol({a}) = vol(Ω) = 1
      rw [← ENNReal.toReal_sum (fun a _ => measure_ne_top volume {a})]
      have huniv : Finset.univ.sum (fun a : Ω => volume ({a} : Set Ω)) =
        volume (Set.univ : Set Ω) := by
        rw [← measure_biUnion_finset
          (fun a _ b _ hab => Set.disjoint_singleton.mpr hab)
          (fun a _ => MeasurableSet.of_discrete)]
        congr 1
        ext x; simp
      rw [huniv, measure_univ]
      simp
    -- Total floor weight ≤ N
    have htotal_le : Finset.univ.sum wt ≤ N := by
      suffices h : ((Finset.univ.sum wt : ℕ) : ℝ) ≤ (N : ℝ) by exact_mod_cast h
      calc ((Finset.univ.sum wt : ℕ) : ℝ)
          = Finset.univ.sum (fun j => (wt j : ℝ)) := by push_cast; rfl
        _ ≤ Finset.univ.sum (fun j => (volume ({e.symm j} : Set Ω)).toReal * N) := by
            apply Finset.sum_le_sum
            intro j _
            exact Nat.floor_le (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))
        _ = (Finset.univ.sum (fun j => (volume ({e.symm j} : Set Ω)).toReal)) * N := by
            rw [Finset.sum_mul]
        _ = 1 * N := by rw [hsum_vol]
        _ = N := one_mul _
    -- wt(e a) = ⌊volume({a}).toReal * N⌋₊ ≤ volume({a}).toReal * N
    have hwt_le : ∀ a : Ω, (wt (e a) : ℝ) ≤ (volume ({a} : Set Ω)).toReal * N := by
      intro a
      simp only [wt, e, Equiv.symm_apply_apply]
      exact Nat.floor_le (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))
    -- Remainder to distribute: r = N - Σ wt(j), so r ≤ k
    set r := N - Finset.univ.sum wt with hr_def
    -- Adjusted weight: first r elements get 1 extra
    set adjWt : Fin k → ℕ := fun j =>
      wt j + if (j : ℕ) < r then 1 else 0
    -- adjWt(j) ≤ wt(j) + 1
    have hadj_le : ∀ j : Fin k, (adjWt j : ℝ) ≤ (wt j : ℝ) + 1 := by
      intro j
      have : adjWt j ≤ wt j + 1 := by simp only [adjWt]; split <;> omega
      exact_mod_cast this
    -- Cumulative weight: cumWt(i) = Σ_{j<i} adjWt(j)
    -- We use Fin.val for the sum range
    set cumWt : ℕ → ℕ := fun i =>
      (Finset.range i).sum (fun j =>
        if h : j < k then adjWt ⟨j, h⟩ else 0) with hcumWt_def
    -- cumWt is monotone
    have hcumWt_mono : ∀ i j, i ≤ j → cumWt i ≤ cumWt j := by
      intro i j hij
      apply Finset.sum_le_sum_of_subset
      exact Finset.range_mono hij
    -- cumWt(k) = N: the total adjusted weight equals N
    have hcumWt_k : cumWt k = N := by
      -- cumWt(k) = Σ_{j<k} adjWt(j) = Σ wt(j) + r = Σ wt(j) + (N - Σ wt(j)) = N
      -- First, show cumWt(k) = Finset.univ.sum adjWt
      have hcum_eq_sum : cumWt k = Finset.univ.sum adjWt := by
        simp only [cumWt]
        -- Reindex: Σ_{j:Fin k} adjWt(j) = Σ_{j∈range k} (dite ...)
        rw [← Finset.sum_fin_eq_sum_range]
      rw [hcum_eq_sum]
      -- Finset.univ.sum adjWt = Finset.univ.sum wt + r = N
      -- Split adjWt into wt part + indicator part
      have hsplit : Finset.univ.sum adjWt =
          Finset.univ.sum wt +
          Finset.univ.sum (fun j : Fin k => if (j : ℕ) < r then 1 else 0) := by
        conv_lhs => arg 2; ext j; rw [show adjWt j = wt j + if (j : ℕ) < r then 1 else 0 from rfl]
        exact Finset.sum_add_distrib
      rw [hsplit]
      -- The indicator sum counts how many j : Fin k have j.val < r
      -- This equals min r k. We need r ≤ k.
      -- For the sum: it equals r when r ≤ k
      -- Proof that Σ indicator = r
      -- First prove r ≤ k
      have hr_le_k : r ≤ k := by
        -- N - Σ wt ≤ k ⟺ N ≤ Σ wt + k ⟺ N - k ≤ Σ wt
        -- wt(j) = ⌊vol(a_j)*N⌋₊ and Σ vol(a_j)*N = N
        -- Each ⌊x⌋₊ ≥ x - 1 when x ≥ 0, so Σ wt ≥ N - k
        suffices h : N ≤ Finset.univ.sum wt + k by omega
        suffices h : (N : ℝ) ≤ ((Finset.univ.sum wt : ℕ) : ℝ) + (k : ℝ) by exact_mod_cast h
        have hfloor_bound : ∀ j : Fin k,
            (volume ({e.symm j} : Set Ω)).toReal * N ≤ (wt j : ℝ) + 1 := by
          intro j
          have := (Nat.lt_floor_add_one ((volume ({e.symm j} : Set Ω)).toReal * N)).le
          simp only [wt] at this ⊢
          exact_mod_cast this
        calc (N : ℝ)
          = Finset.univ.sum (fun j : Fin k =>
              (volume ({e.symm j} : Set Ω)).toReal * N) := by
              rw [← Finset.sum_mul, hsum_vol, one_mul]
          _ ≤ Finset.univ.sum (fun j => (wt j : ℝ) + 1) := by
              apply Finset.sum_le_sum; intro j _; linarith [hfloor_bound j]
          _ = ((Finset.univ.sum wt : ℕ) : ℝ) + (k : ℝ) := by
              push_cast
              rw [Finset.sum_add_distrib]
              simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      have hind : Finset.univ.sum (fun j : Fin k => if (j : ℕ) < r then 1 else 0) = r := by
        -- Rewrite sum of indicators as filter cardinality
        rw [← Finset.card_filter]
        -- Goal: (Finset.univ.filter (fun j : Fin k => (j : ℕ) < r)).card = r
        -- These are ⟨0,_⟩, ..., ⟨r-1,_⟩, so card = r (since r ≤ k)
        rcases eq_or_lt_of_le hr_le_k with hrk | hr_lt
        · -- r = k: all elements of Fin k satisfy val < k
          rw [hrk]
          have : Finset.univ.filter (fun j : Fin k => (j : ℕ) < k) = Finset.univ :=
            Finset.filter_true_of_mem (fun j _ => j.isLt)
          rw [this, Finset.card_univ, Fintype.card_fin]
        · -- r < k: the filter equals Finset.Iio ⟨r, hr_lt⟩
          have : Finset.univ.filter (fun j : Fin k => (j : ℕ) < r) =
              Finset.Iio (⟨r, hr_lt⟩ : Fin k) := by
            ext j; simp [Fin.lt_iff_val_lt_val]
          rw [this]; simp
      rw [hind, hr_def]
      exact Nat.add_sub_cancel' htotal_le
    -- For each j < k, cumWt(j+1) = cumWt(j) + adjWt(j)
    have hcumWt_succ : ∀ j : Fin k,
        cumWt (j.val + 1) = cumWt j.val + adjWt j := by
      intro j
      simp only [cumWt, Finset.sum_range_succ]
      congr 1
      simp [j.isLt]
    -- Define φ using the inverse CDF: for m : Fin N, find which interval it's in
    -- φ(ω) = e.symm(j) where cumWt(j) ≤ eN(ω) < cumWt(j+1)
    -- We use the modMap as a fallback and prove the bound
    -- Actually, define φ directly: for each m, find the right bucket
    -- Define bucket: the unique j such that cumWt(j) ≤ m < cumWt(j+1)
    -- We define it as: bucket(m) = (number of j < k with cumWt(j+1) ≤ m)
    -- This gives the correct bucket since cumWt is monotone
    -- Simpler: define bucket(m) = min(k-1, Σ_{j < k} [cumWt(j+1) ≤ m])
    -- Actually, let's just define it directly
    -- For m : Fin N, define bucket(m) = largest j < k such that cumWt(j) ≤ m
    -- This is well-defined since cumWt(0) = 0 ≤ m
    have hcumWt_zero : cumWt 0 = 0 := by
      simp [cumWt]
    -- Define the bucket function: for m : Fin N, find which interval it belongs to.
    -- bucket(m) = (number of i in {0,...,k-1} with cumWt(i+1) ≤ m)
    -- This is < k because m < N = cumWt(k), so not all k intervals precede m.
    -- Key property: bucket(m) = j ↔ cumWt(j) ≤ m < cumWt(j+1)
    -- The fiber over j has exactly adjWt(j) elements.

    -- We need a helper lemma: for m < N, the count is < k
    have hbucket_lt : ∀ m : Fin N,
        ((Finset.range k).filter (fun i => cumWt (i + 1) ≤ m.val)).card < k := by
      intro m
      -- If the count were = k, then all cumWt(i+1) ≤ m for i < k,
      -- in particular cumWt(k) ≤ m. But m < N = cumWt(k), contradiction.
      by_contra h
      push_neg at h
      have hle := Finset.card_filter_le (Finset.range k) (fun i => cumWt (i + 1) ≤ m.val)
      simp at hle
      -- So the count equals k
      have hcount_eq : ((Finset.range k).filter (fun i => cumWt (i + 1) ≤ m.val)).card = k := by
        omega
      -- Every element of range k is in the filter
      have hfilter_eq : (Finset.range k).filter (fun i => cumWt (i + 1) ≤ m.val) = Finset.range k := by
        rw [Finset.filter_eq_self]
        intro i hi
        -- All elements must be in filter since card of filter = card of range k
        -- and filter ⊆ range k
        by_contra hni
        have : ((Finset.range k).filter (fun i => cumWt (i + 1) ≤ m.val)).card < (Finset.range k).card := by
          exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨i, hi, hni⟩)
        simp at this
        omega
      -- In particular, k-1 is in the filter (if k > 0)
      have hk_pos' : 0 < k := Fintype.card_pos
      have : k - 1 ∈ (Finset.range k).filter (fun i => cumWt (i + 1) ≤ m.val) := by
        rw [hfilter_eq]; simp; omega
      simp at this
      -- So cumWt(k-1+1) ≤ m, and since k > 0, k-1+1 = k
      have hk_pos' : 0 < k := Fintype.card_pos
      have hkk : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk_pos'
      -- cumWt(k) ≤ m
      have hcumk : cumWt k ≤ m.val := by rw [← hkk]; exact this.2
      -- But m < N = cumWt(k)
      linarith [m.isLt, hcumWt_k]

    set bucket : Fin N → Fin k := fun m =>
      ⟨((Finset.range k).filter (fun i => cumWt (i + 1) ≤ m.val)).card,
        hbucket_lt m⟩ with hbucket_def

    -- The fiber over j has size ≤ adjWt(j)
    -- (In fact it has size exactly adjWt(j), but ≤ suffices)
    have hfiber_le : ∀ j : Fin k,
        (Finset.univ.filter (fun m : Fin N => bucket m = j)).card ≤ adjWt j := by
      -- The fiber of j consists of m with cumWt(j) ≤ m < cumWt(j+1),
      -- which is an interval of size cumWt(j+1) - cumWt(j) = adjWt(j).
      sorry

    -- Define φ
    refine ⟨fun ω => e.symm (bucket (eN ω)), fun a => ?_⟩
    -- The fiber over a: {ω | e.symm(bucket(eN(ω))) = a} has same card as
    -- {m : Fin N | bucket(m) = e(a)} since eN is a bijection.
    -- Use Finset.card_map or Equiv to transfer
    have hfiber : (Finset.univ.filter (fun ω : CoinTape n =>
        e.symm (bucket (eN ω)) = a)).card =
      (Finset.univ.filter (fun m : Fin N => bucket m = e a)).card := by
      -- The map eN gives a bijection between the two filter sets
      have : (Finset.univ.filter (fun ω : CoinTape n =>
          e.symm (bucket (eN ω)) = a)) =
        (Finset.univ.filter (fun m : Fin N => bucket m = e a)).map eN.symm.toEmbedding := by
        ext ω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
          Equiv.toEmbedding_apply]
        constructor
        · intro h
          exact ⟨eN ω, by rwa [e.symm_apply_eq] at h, by simp⟩
        · rintro ⟨m, hm, rfl⟩
          simp [Equiv.symm_apply_apply, hm]
      rw [this, Finset.card_map]
    rw [hfiber]
    -- Now bound: card ≤ adjWt(e a) ≤ wt(e a) + 1 ≤ volume({a}).toReal * N + 1
    calc ((Finset.univ.filter (fun m : Fin N => bucket m = e a)).card : ℝ)
        ≤ adjWt (e a) := by exact_mod_cast hfiber_le (e a)
      _ ≤ wt (e a) + 1 := hadj_le (e a)
      _ ≤ (volume ({a} : Set Ω)).toReal * N + 1 := by linarith [hwt_le a]
  obtain ⟨φ, hφ⟩ := key
  refine ⟨n, φ, fun S => ?_⟩
  -- The measure bound: volume(φ⁻¹(S)) ≤ volume(S) + k/2^n < volume(S) + δ
  -- Key idea: each fiber φ⁻¹({a}) has size ≤ volume({a}) * 2^n + 1
  -- Summing: |φ⁻¹(S)| ≤ volume(S) * 2^n + |S| ≤ volume(S) * 2^n + k
  -- Dividing by 2^n gives the bound
  -- Step 1: Express volume on CoinTape as count / N
  set N := Fintype.card (CoinTape n) with hN_def
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr Fintype.card_pos
  have hN_eq : (N : ℝ) = 2 ^ n := by
    simp [hN_def, CoinTape,
      Fintype.card_bool, Fintype.card_fin]
  have hvol : volume (φ ⁻¹' S : Set (CoinTape n)) =
      Measure.count (φ ⁻¹' S : Set (CoinTape n)) / ↑N := by
    change ProbabilityTheory.uniformOn Set.univ _ = _
    rw [ProbabilityTheory.uniformOn_univ]
  -- Step 2: Bound count(φ⁻¹(S)).toReal / N ≤ volume(S).toReal + k/2^n
  have step1 : (volume (φ ⁻¹' S : Set (CoinTape n))).toReal ≤
      (volume S).toReal + (k : ℝ) / 2 ^ n := by
    rw [hvol, ENNReal.toReal_div]
    -- Goal: count(φ⁻¹(S)).toReal / N.toReal ≤ volume(S).toReal + k / 2^n
    sorry
  linarith
