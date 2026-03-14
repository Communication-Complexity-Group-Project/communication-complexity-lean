import CommunicationComplexity.LowerBounds.Rectangles

namespace DetProtocol

variable {X Y α : Type}

/-- A set of rectangles that partitions `X × Y` (without monochromaticity data). -/
def isRectPartition (Part : Set (Set (X × Y))) : Prop :=
  (∀ R ∈ Part, isRectangle R) ∧
  ⋃₀ Part = Set.univ ∧
  (∀ R S, R ∈ Part → S ∈ Part → R ≠ S → Disjoint R S)

namespace isRectPartition

variable {Part : Set (Set (X × Y))}

theorem exists_mem (h : isRectPartition Part) (p : X × Y) :
    ∃ R ∈ Part, p ∈ R := by
  have hp : p ∈ ⋃₀ Part := by simp [h.2.1]
  exact Set.mem_sUnion.mp hp

theorem eq_of_mem (h : isRectPartition Part)
    {R S : Set (X × Y)} (hR : R ∈ Part) (hS : S ∈ Part)
    {p : X × Y} (hpR : p ∈ R) (hpS : p ∈ S) : R = S := by
  by_contra hne
  exact Set.disjoint_left.mp (h.2.2 R S hR hS hne) hpR hpS

end isRectPartition

theorem isRectPartition_of_isMonoRectPartition
    {Part : Set (Set (X × Y))} {g : X → Y → α}
    (h : isMonoRectPartition Part g) : isRectPartition Part :=
  ⟨h.1, h.2.2.1, h.2.2.2⟩

section RectOf

variable {Part : Set (Set (X × Y))} (hPart : isRectPartition Part)

/-- The unique rectangle of the partition containing `(x,y)`. -/
noncomputable def rectOf (x : X) (y : Y) : Set (X × Y) :=
  Classical.choose (hPart.exists_mem (x, y))

theorem rectOf_mem (x : X) (y : Y) : rectOf hPart x y ∈ Part :=
  (Classical.choose_spec (hPart.exists_mem (x, y))).1

theorem rectOf_contains (x : X) (y : Y) : (x, y) ∈ rectOf hPart x y :=
  (Classical.choose_spec (hPart.exists_mem (x, y))).2

theorem rectOf_eq_of_mem {R : Set (X × Y)} (hR : R ∈ Part)
    {x : X} {y : Y} (hxy : (x, y) ∈ R) :
    rectOf hPart x y = R := by
  exact hPart.eq_of_mem (rectOf_mem hPart x y) hR
    (rectOf_contains hPart x y) hxy

end RectOf

section Theorem19

variable {Part : Set (Set (X × Y))}
variable (hPart : isRectPartition Part) (hFin : Part.Finite)

abbrev RectIn := {R : Set (X × Y) // R ∈ Part}

noncomputable instance : Fintype (RectIn (Part := Part)) :=
  hFin.fintype

def hIntersects (R S : RectIn (Part := Part)) : Prop :=
  ∃ x y y', (x, y) ∈ R.1 ∧ (x, y') ∈ S.1

def vIntersects (R S : RectIn (Part := Part)) : Prop :=
  ∃ x x' y, (x, y) ∈ R.1 ∧ (x', y) ∈ S.1

theorem disjoint_rectangles_not_both_intersections
    (hPart : isRectPartition Part)
    {R S : RectIn (Part := Part)} (hdisj : Disjoint R.1 S.1) :
    ¬ (hIntersects (Part := Part) R S ∧ vIntersects (Part := Part) R S) := by
  intro hBoth
  rcases hBoth with ⟨hH, hV⟩
  rcases hH with ⟨x, yR, yS, hxyR, hxyS⟩
  rcases hV with ⟨xR, xS, y, hxRy, hxSy⟩
  have hRectR : isRectangle R.1 := hPart.1 R.1 R.2
  have hRectS : isRectangle S.1 := hPart.1 S.1 S.2
  have hcrossR := (isRectangle_iff (X := X) (Y := Y) R.1).mp hRectR
  have hcrossS := (isRectangle_iff (X := X) (Y := Y) S.1).mp hRectS
  have hxy_in_R : (x, y) ∈ R.1 := (hcrossR x xR yR y hxyR hxRy).2
  have hxy_in_S : (x, y) ∈ S.1 := (hcrossS x xS yS y hxyS hxSy).2
  exact Set.disjoint_left.mp hdisj hxy_in_R hxy_in_S

def hNext (C : Set (RectIn (Part := Part))) (R : RectIn (Part := Part)) :
    Set (RectIn (Part := Part)) :=
  {S | S ∈ C ∧ hIntersects (Part := Part) S R}

def vNext (C : Set (RectIn (Part := Part))) (R : RectIn (Part := Part)) :
    Set (RectIn (Part := Part)) :=
  {S | S ∈ C ∧ vIntersects (Part := Part) S R}

def xConsistent (x : X) (R : RectIn (Part := Part)) : Prop :=
  ∃ y, (x, y) ∈ R.1

def yConsistent (y : Y) (R : RectIn (Part := Part)) : Prop :=
  ∃ x, (x, y) ∈ R.1

def hGood (C : Set (RectIn (Part := Part))) (R : RectIn (Part := Part)) : Prop :=
  (hNext (Part := Part) C R).ncard ≤ (C.ncard + 1) / 2

def vGood (C : Set (RectIn (Part := Part))) (R : RectIn (Part := Part)) : Prop :=
  (vNext (Part := Part) C R).ncard ≤ (C.ncard + 1) / 2

lemma hIntersects_self_of_xConsistent {x : X} {R : RectIn (Part := Part)}
    (h : xConsistent (Part := Part) x R) :
    hIntersects (Part := Part) R R := by
  rcases h with ⟨y, hxy⟩
  exact ⟨x, y, y, hxy, hxy⟩

lemma vIntersects_self_of_yConsistent {y : Y} {R : RectIn (Part := Part)}
    (h : yConsistent (Part := Part) y R) :
    vIntersects (Part := Part) R R := by
  rcases h with ⟨x, hxy⟩
  exact ⟨x, x, y, hxy, hxy⟩

lemma hIntersects_of_xConsistent {x : X}
    {R S : RectIn (Part := Part)}
    (hR : xConsistent (Part := Part) x R)
    (hS : xConsistent (Part := Part) x S) :
    hIntersects (Part := Part) R S := by
  rcases hR with ⟨yR, hxyR⟩
  rcases hS with ⟨yS, hxyS⟩
  exact ⟨x, yR, yS, hxyR, hxyS⟩

lemma vIntersects_of_yConsistent {y : Y}
    {R S : RectIn (Part := Part)}
    (hR : yConsistent (Part := Part) y R)
    (hS : yConsistent (Part := Part) y S) :
    vIntersects (Part := Part) R S := by
  rcases hR with ⟨xR, hxRy⟩
  rcases hS with ⟨xS, hxSy⟩
  exact ⟨xR, xS, y, hxRy, hxSy⟩

lemma hnext_union_vnext_card_le (C : Set (RectIn (Part := Part)))
    (T : RectIn (Part := Part))
    (hPart : isRectPartition Part) (hFin : Part.Finite) :
    (hNext (Part := Part) C T).ncard + (vNext (Part := Part) C T).ncard ≤ C.ncard + 1 := by
  letI : Fintype (RectIn (Part := Part)) := hFin.fintype
  have hUnionSub :
      hNext (Part := Part) C T ∪ vNext (Part := Part) C T ⊆ C := by
    intro R hR
    rcases hR with hR | hR <;> exact hR.1
  have hUnionLe :
      (hNext (Part := Part) C T ∪ vNext (Part := Part) C T).ncard ≤ C.ncard :=
    Set.ncard_le_ncard hUnionSub
  have hInterSub :
      hNext (Part := Part) C T ∩ vNext (Part := Part) C T ⊆ ({T} : Set (RectIn (Part := Part))) := by
    intro R hR
    rcases hR with ⟨hRH, hRV⟩
    by_cases hEq : R = T
    · simp [hEq]
    · exfalso
      have hneSet : R.1 ≠ T.1 := by
        intro h
        apply hEq
        exact Subtype.ext h
      have hDisj : Disjoint R.1 T.1 := hPart.2.2 R.1 T.1 R.2 T.2 hneSet
      exact (disjoint_rectangles_not_both_intersections (Part := Part) hPart hDisj)
        ⟨hRH.2, hRV.2⟩
  have hInterLe :
      (hNext (Part := Part) C T ∩ vNext (Part := Part) C T).ncard ≤ 1 := by
    calc
      (hNext (Part := Part) C T ∩ vNext (Part := Part) C T).ncard
          ≤ ({T} : Set (RectIn (Part := Part))).ncard := Set.ncard_le_ncard hInterSub
      _ = 1 := Set.ncard_singleton T
  calc
    (hNext (Part := Part) C T).ncard + (vNext (Part := Part) C T).ncard
        = (hNext (Part := Part) C T ∪ vNext (Part := Part) C T).ncard
          + (hNext (Part := Part) C T ∩ vNext (Part := Part) C T).ncard := by
            simpa using (Set.ncard_union_add_ncard_inter
              (hNext (Part := Part) C T) (vNext (Part := Part) C T)).symm
    _ ≤ C.ncard + 1 := by exact Nat.add_le_add hUnionLe hInterLe

lemma exists_good (C : Set (RectIn (Part := Part))) (T : RectIn (Part := Part))
    (hPart : isRectPartition Part) (hFin : Part.Finite) :
    hGood (Part := Part) C T ∨ vGood (Part := Part) C T := by
  letI : Fintype (RectIn (Part := Part)) := hFin.fintype
  unfold hGood vGood
  by_cases hH : (hNext (Part := Part) C T).ncard ≤ (C.ncard + 1) / 2
  · exact Or.inl hH
  · have hHgt : (C.ncard + 1) / 2 < (hNext (Part := Part) C T).ncard :=
      Nat.lt_of_not_ge hH
    have hSum := hnext_union_vnext_card_le (Part := Part) C T hPart hFin
    have hV : (vNext (Part := Part) C T).ncard ≤ (C.ncard + 1) / 2 := by
      by_contra hV
      have hVgt : (C.ncard + 1) / 2 < (vNext (Part := Part) C T).ncard :=
        Nat.lt_of_not_ge hV
      omega
    exact Or.inr hV

lemma half_le_pow_pred {n k : ℕ} (hn : n ≤ 2 ^ (k + 1)) :
    (n + 1) / 2 ≤ 2 ^ k := by
  have hn' : n ≤ 2 * (2 ^ k) := by
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn
  omega

def hPred (C : Set (RectIn (Part := Part))) (x : X)
    (R : RectIn (Part := Part)) : Prop :=
  R ∈ C ∧ xConsistent (Part := Part) x R ∧ hGood (Part := Part) C R

def vPred (C : Set (RectIn (Part := Part))) (y : Y)
    (R : RectIn (Part := Part)) : Prop :=
  R ∈ C ∧ yConsistent (Part := Part) y R ∧ vGood (Part := Part) C R

noncomputable def hCand (C : Set (RectIn (Part := Part))) (x : X) :
    Option (RectIn (Part := Part)) :=
  by
    classical
    exact if h : ∃ R, hPred (Part := Part) C x R then some (Classical.choose h) else none

noncomputable def vCand (C : Set (RectIn (Part := Part))) (y : Y) :
    Option (RectIn (Part := Part)) :=
  by
    classical
    exact if h : ∃ R, vPred (Part := Part) C y R then some (Classical.choose h) else none

lemma hCand_spec_some {C : Set (RectIn (Part := Part))} {x : X}
    {R : RectIn (Part := Part)} (hR : hCand (Part := Part) C x = some R) :
    hPred (Part := Part) C x R := by
  classical
  unfold hCand at hR
  split_ifs at hR with h
  · injection hR with hEq
    subst hEq
    exact Classical.choose_spec h

lemma vCand_spec_some {C : Set (RectIn (Part := Part))} {y : Y}
    {R : RectIn (Part := Part)} (hR : vCand (Part := Part) C y = some R) :
    vPred (Part := Part) C y R := by
  classical
  unfold vCand at hR
  split_ifs at hR with h
  · injection hR with hEq
    subst hEq
    exact Classical.choose_spec h

lemma hCand_eq_none_iff {C : Set (RectIn (Part := Part))} {x : X} :
    hCand (Part := Part) C x = none ↔ ¬ ∃ R, hPred (Part := Part) C x R := by
  classical
  unfold hCand
  split_ifs <;> simp [*]

lemma vCand_eq_none_iff {C : Set (RectIn (Part := Part))} {y : Y} :
    vCand (Part := Part) C y = none ↔ ¬ ∃ R, vPred (Part := Part) C y R := by
  classical
  unfold vCand
  split_ifs <;> simp [*]

noncomputable def chooseOut (C : Set (RectIn (Part := Part))) : Set (X × Y) :=
  by
    classical
    exact if h : ∃ R, R ∈ C then (Classical.choose h).1 else Set.univ

lemma chooseOut_eq_of_mem_card_le_one {C : Set (RectIn (Part := Part))}
    {T : RectIn (Part := Part)} (hFin : Part.Finite)
    (hT : T ∈ C) (hCard : C.ncard ≤ 1) :
    chooseOut (Part := Part) C = T.1 := by
  classical
  letI : Fintype (RectIn (Part := Part)) := hFin.fintype
  have hEx : ∃ R, R ∈ C := ⟨T, hT⟩
  have hSubsingleton : ∀ {A B : RectIn (Part := Part)}, A ∈ C → B ∈ C → A = B := by
    exact (Set.ncard_le_one_iff (s := C)).1 hCard
  have hChoose : Classical.choose hEx = T := hSubsingleton (Classical.choose_spec hEx) hT
  unfold chooseOut
  simp [hEx, hChoose]

noncomputable def protocolAux (hFin : Part.Finite) :
    ℕ → Set (RectIn (Part := Part)) → DetProtocolGeneralized X Y (Set (X × Y))
  | 0, C => .output (chooseOut (Part := Part) C)
  | k + 1, C =>
      by
        classical
        letI : Fintype (RectIn (Part := Part)) := hFin.fintype
        exact DetProtocolGeneralized.alice (β := Option (RectIn (Part := Part)))
          (fun x => hCand (Part := Part) C x) (fun a : Option (RectIn (Part := Part)) =>
            match a with
            | some r => protocolAux hFin k (hNext (Part := Part) C r)
            | none =>
                DetProtocolGeneralized.bob (β := Option (RectIn (Part := Part)))
                  (fun y => vCand (Part := Part) C y) (fun b : Option (RectIn (Part := Part)) =>
                    match b with
                    | some r => protocolAux hFin k (vNext (Part := Part) C r)
                    | none => DetProtocolGeneralized.output (chooseOut (Part := Part) C)))

noncomputable def msgCost (hFin : Part.Finite) : ℕ := by
  classical
  letI : Fintype (RectIn (Part := Part)) := hFin.fintype
  exact Nat.clog 2 (Fintype.card (Option (RectIn (Part := Part))))

lemma protocolAux_complexity_le (hFin : Part.Finite) (k : ℕ) (C : Set (RectIn (Part := Part))) :
    (protocolAux (Part := Part) hFin k C).complexity ≤ 2 * k * msgCost (Part := Part) hFin := by
  classical
  letI : Fintype (RectIn (Part := Part)) := hFin.fintype
  induction k generalizing C with
  | zero =>
    simp [protocolAux, DetProtocolGeneralized.complexity]
  | succ k ih =>
    let m := msgCost (Part := Part) hFin
    simp only [protocolAux, DetProtocolGeneralized.complexity]
    change m + Finset.univ.sup
        (fun a : Option (RectIn (Part := Part)) =>
          (match a with
           | some r => protocolAux hFin k (hNext (Part := Part) C r)
           | none =>
               DetProtocolGeneralized.bob (β := Option (RectIn (Part := Part)))
                 (fun y => vCand (Part := Part) C y) (fun b =>
                   match b with
                   | some r => protocolAux hFin k (vNext (Part := Part) C r)
                   | none => DetProtocolGeneralized.output (chooseOut (Part := Part) C))).complexity)
      ≤ 2 * (k + 1) * m
    have hSup :
        Finset.univ.sup
          (fun a : Option (RectIn (Part := Part)) =>
            (match a with
             | some r => protocolAux hFin k (hNext (Part := Part) C r)
             | none =>
                 DetProtocolGeneralized.bob (β := Option (RectIn (Part := Part)))
                   (fun y => vCand (Part := Part) C y) (fun b =>
                     match b with
                     | some r => protocolAux hFin k (vNext (Part := Part) C r)
                     | none => DetProtocolGeneralized.output (chooseOut (Part := Part) C))).complexity)
        ≤ m + 2 * k * m := by
      apply Finset.sup_le
      intro a ha
      cases a with
      | none =>
        have hBobSup :
            ∀ b : Option (RectIn (Part := Part)), b ∈ Finset.univ →
              (match b with
               | some r => protocolAux (Part := Part) hFin k (vNext (Part := Part) C r)
               | none =>
                   DetProtocolGeneralized.output (X := X) (Y := Y) (α := Set (X × Y))
                     (chooseOut (Part := Part) C)).complexity ≤ 2 * k * m := by
          intro b hb
          cases b with
          | none =>
            simpa [DetProtocolGeneralized.complexity] using
              (Nat.zero_le (2 * k * m))
          | some r => simpa [m] using ih (vNext (Part := Part) C r)
        have hBobSupLe :
            Finset.univ.sup (fun b : Option (RectIn (Part := Part)) =>
              (match b with
               | some r => protocolAux (Part := Part) hFin k (vNext (Part := Part) C r)
               | none =>
                   DetProtocolGeneralized.output (X := X) (Y := Y) (α := Set (X × Y))
                     (chooseOut (Part := Part) C)).complexity)
              ≤ 2 * k * m := by
          exact (Finset.sup_le_iff).2 hBobSup
        have hm : Nat.clog 2 (Fintype.card (Option (RectIn (Part := Part)))) = m := rfl
        rw [DetProtocolGeneralized.complexity, hm]
        exact Nat.add_le_add_left hBobSupLe m
      | some r =>
        have hRec : (protocolAux (Part := Part) hFin k (hNext (Part := Part) C r)).complexity
            ≤ 2 * k * m := by simpa [m] using ih (hNext (Part := Part) C r)
        exact hRec.trans (by omega)
    calc
      m + Finset.univ.sup
          (fun a : Option (RectIn (Part := Part)) =>
            (match a with
             | some r => protocolAux hFin k (hNext (Part := Part) C r)
             | none =>
                 DetProtocolGeneralized.bob (β := Option (RectIn (Part := Part)))
                   (fun y => vCand (Part := Part) C y) (fun b =>
                     match b with
                     | some r => protocolAux hFin k (vNext (Part := Part) C r)
                     | none => DetProtocolGeneralized.output (chooseOut (Part := Part) C))).complexity)
          ≤ m + (m + 2 * k * m) := Nat.add_le_add_left hSup _
      _ = 2 * (k + 1) * m := by ring

noncomputable def rectOfIn (x : X) (y : Y) : RectIn (Part := Part) :=
  ⟨rectOf hPart x y, rectOf_mem hPart x y⟩

lemma rectOfIn_contains (x : X) (y : Y) :
    (x, y) ∈ (rectOfIn (Part := Part) hPart x y).1 :=
  rectOf_contains hPart x y

lemma protocolAux_correct
    (hPart : isRectPartition Part) (hFin : Part.Finite)
    (k : ℕ) (C : Set (RectIn (Part := Part))) (T : RectIn (Part := Part))
    (x : X) (y : Y)
    (hT : T ∈ C)
    (hxyT : (x, y) ∈ T.1)
    (hCard : C.ncard ≤ 2 ^ k) :
    (protocolAux (Part := Part) hFin k C).run x y = T.1 := by
  classical
  letI : Fintype (RectIn (Part := Part)) := hFin.fintype
  induction k generalizing C T with
  | zero =>
    have hC1 : C.ncard ≤ 1 := by simpa using hCard
    simpa [protocolAux] using
      chooseOut_eq_of_mem_card_le_one (Part := Part) (C := C) (T := T) hFin hT hC1
  | succ k ih =>
    simp only [protocolAux, DetProtocolGeneralized.run]
    set a : Option (RectIn (Part := Part)) := hCand (Part := Part) C x
    cases ha : a with
    | some R =>
      have hPredR : hPred (Part := Part) C x R := by
        simpa [a] using hCand_spec_some (Part := Part) (C := C) (x := x) ha
      have hTnext : T ∈ hNext (Part := Part) C R := by
        refine ⟨hT, ?_⟩
        exact hIntersects_of_xConsistent (Part := Part)
          ⟨y, hxyT⟩ hPredR.2.1
      have hCardNext : (hNext (Part := Part) C R).ncard ≤ 2 ^ k := by
        exact hPredR.2.2.trans (half_le_pow_pred (by simpa [Nat.pow_succ] using hCard))
      simpa [a, ha] using
        ih (C := hNext (Part := Part) C R) (T := T) hTnext hxyT hCardNext
    | none =>
      have hNoAlice : ¬ ∃ R, hPred (Part := Part) C x R := by
        exact (hCand_eq_none_iff (Part := Part) (C := C) (x := x)).mp (by simpa [a] using ha)
      have hGoodOr : hGood (Part := Part) C T ∨ vGood (Part := Part) C T :=
        exists_good (Part := Part) C T hPart hFin
      have hVGoodT : vGood (Part := Part) C T := by
        cases hGoodOr with
        | inl hH =>
          have : ∃ R, hPred (Part := Part) C x R := ⟨T, hT, ⟨y, hxyT⟩, hH⟩
          exact (False.elim (hNoAlice this))
        | inr hV => exact hV
      have hBobExists : ∃ R, vPred (Part := Part) C y R := ⟨T, hT, ⟨x, hxyT⟩, hVGoodT⟩
      set b : Option (RectIn (Part := Part)) := vCand (Part := Part) C y
      have hb_not_none : b ≠ none := by
        intro hb0
        have hNoBob : ¬ ∃ R, vPred (Part := Part) C y R := by
          exact (vCand_eq_none_iff (Part := Part) (C := C) (y := y)).mp (by simpa [b] using hb0)
        exact hNoBob hBobExists
      cases hb : b with
      | none =>
        exact (hb_not_none hb).elim
      | some R =>
        have hPredR : vPred (Part := Part) C y R := by
          simpa [b] using vCand_spec_some (Part := Part) (C := C) (y := y) hb
        have hTnext : T ∈ vNext (Part := Part) C R := by
          refine ⟨hT, ?_⟩
          exact vIntersects_of_yConsistent (Part := Part)
            ⟨x, hxyT⟩ hPredR.2.1
        have hCardNext : (vNext (Part := Part) C R).ncard ≤ 2 ^ k := by
          exact hPredR.2.2.trans (half_le_pow_pred (by simpa [Nat.pow_succ] using hCard))
        simpa [a, ha, b, hb, DetProtocolGeneralized.run] using
          ih (C := vNext (Part := Part) C R) (T := T) hTnext hxyT hCardNext

lemma msgCost_le_succ
    (hFin : Part.Finite)
    {c : ℕ} (hc : Set.ncard Part ≤ 2 ^ c) :
    msgCost (Part := Part) hFin ≤ c + 1 := by
  classical
  letI : Fintype (RectIn (Part := Part)) := hFin.fintype
  have hRectCard : Fintype.card (RectIn (Part := Part)) = Set.ncard Part := by
    calc
      Fintype.card (RectIn (Part := Part)) = (hFin.toFinset).card := by
        simpa [RectIn] using (Set.toFinset_card (s := Part))
      _ = Set.ncard Part := by
        simpa using (Set.ncard_eq_toFinset_card (s := Part) hFin).symm
  have hOptCard : Fintype.card (Option (RectIn (Part := Part)))
      ≤ 2 ^ (c + 1) := by
    have hPartLe : Fintype.card (RectIn (Part := Part)) ≤ 2 ^ c := by
      simpa [hRectCard] using hc
    calc
      Fintype.card (Option (RectIn (Part := Part)))
          = Fintype.card (RectIn (Part := Part)) + 1 := by simp
      _ ≤ 2 ^ c + 1 := Nat.succ_le_succ hPartLe
      _ ≤ 2 ^ (c + 1) := by
        have h1 : 1 ≤ 2 ^ c := Nat.succ_le_of_lt (Nat.two_pow_pos c)
        calc
          2 ^ c + 1 ≤ 2 ^ c + 2 ^ c := Nat.add_le_add_left h1 _
          _ = 2 ^ (c + 1) := by
            simp [Nat.pow_succ, two_mul, Nat.mul_comm]
  have hclog :
      Nat.clog 2 (Fintype.card (Option (RectIn (Part := Part)))) ≤ c + 1 := by
    exact (Nat.clog_le_iff_le_pow (by decide)).2 hOptCard
  simpa [msgCost] using hclog

lemma ncard_univ_rectIn :
    ∀ (hFin : Part.Finite), (Set.univ : Set (RectIn (Part := Part))).ncard = Set.ncard Part := by
  intro hFin
  classical
  letI : Fintype (RectIn (Part := Part)) := hFin.fintype
  calc
    (Set.univ : Set (RectIn (Part := Part))).ncard = Fintype.card (RectIn (Part := Part)) := by
      simpa using Set.ncard_univ (RectIn (Part := Part))
    _ = (hFin.toFinset).card := by
      simpa [RectIn] using (Set.toFinset_card (s := Part))
    _ = Set.ncard Part := by
      simpa using (Set.ncard_eq_toFinset_card (s := Part) hFin).symm

/-- Theorem 1.9 (Rao–Yehudayoff): a partition into at most `2^c` rectangles
yields a deterministic protocol for identifying the containing rectangle using
`O(c^2)` communication (here with explicit bound `2 * (c + 1)^2`). -/
theorem det_cc_rectOf_le_sq_of_rect_partition
    (hPart : isRectPartition Part) (hFin : Part.Finite)
    {c : ℕ} (hc : Set.ncard Part ≤ 2 ^ c) :
    deterministic_communication_complexity (rectOf hPart) ≤ (2 * (c + 1) ^ 2 : ℕ) := by
  classical
  letI : Fintype (RectIn (Part := Part)) := hFin.fintype
  rw [det_cc_le_iff_generalized]
  refine ⟨protocolAux (Part := Part) hFin c Set.univ, ?_, ?_⟩
  · funext x
    funext y
    have hRectUniv :
        (Set.univ : Set (RectIn (Part := Part))).ncard ≤ 2 ^ c := by
      simpa [ncard_univ_rectIn (Part := Part) hFin] using hc
    have hTUniv : rectOfIn (Part := Part) hPart x y ∈ (Set.univ : Set (RectIn (Part := Part))) := by
      simp
    have hxyT : (x, y) ∈ (rectOfIn (Part := Part) hPart x y).1 :=
      rectOfIn_contains (Part := Part) hPart x y
    simpa [rectOfIn] using
      protocolAux_correct (Part := Part) hPart hFin c Set.univ
        (rectOfIn (Part := Part) hPart x y) x y hTUniv hxyT hRectUniv
  · have hComp := protocolAux_complexity_le (Part := Part) hFin c Set.univ
    have hMsg := msgCost_le_succ (Part := Part) hFin (c := c) hc
    calc
      (protocolAux (Part := Part) hFin c Set.univ).complexity
          ≤ 2 * c * msgCost (Part := Part) hFin := hComp
      _ ≤ 2 * c * (c + 1) := by
          exact Nat.mul_le_mul_left (2 * c) hMsg
      _ ≤ 2 * (c + 1) * (c + 1) := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (c + 1) (Nat.le_succ c))
      _ = 2 * (c + 1) ^ 2 := by ring

/-- Convenient restatement of Theorem 1.9 with an explicit protocol witness. -/
theorem rectangle_partition_upper
    (hPart : isRectPartition Part) (hFin : Part.Finite)
    {c : ℕ} (hc : Set.ncard Part ≤ 2 ^ c) :
    ∃ p : DetProtocolGeneralized X Y (Set (X × Y)),
      p.run = rectOf hPart ∧ p.complexity ≤ (2 * (c + 1) ^ 2 : ℕ) := by
  classical
  letI : Fintype (RectIn (Part := Part)) := hFin.fintype
  refine ⟨protocolAux (Part := Part) hFin c Set.univ, ?_, ?_⟩
  · funext x
    funext y
    have hRectUniv :
        (Set.univ : Set (RectIn (Part := Part))).ncard ≤ 2 ^ c := by
      simpa [ncard_univ_rectIn (Part := Part) hFin] using hc
    have hTUniv : rectOfIn (Part := Part) hPart x y ∈ (Set.univ : Set (RectIn (Part := Part))) := by
      simp
    have hxyT : (x, y) ∈ (rectOfIn (Part := Part) hPart x y).1 :=
      rectOfIn_contains (Part := Part) hPart x y
    simpa [rectOfIn] using
      protocolAux_correct (Part := Part) hPart hFin c Set.univ
        (rectOfIn (Part := Part) hPart x y) x y hTUniv hxyT hRectUniv
  · have hComp := protocolAux_complexity_le (Part := Part) hFin c Set.univ
    have hMsg := msgCost_le_succ (Part := Part) hFin (c := c) hc
    calc
      (protocolAux (Part := Part) hFin c Set.univ).complexity
          ≤ 2 * c * msgCost (Part := Part) hFin := hComp
      _ ≤ 2 * c * (c + 1) := by
          exact Nat.mul_le_mul_left (2 * c) hMsg
      _ ≤ 2 * (c + 1) * (c + 1) := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (c + 1) (Nat.le_succ c))
      _ = 2 * (c + 1) ^ 2 := by ring

theorem mono_rectangle_partition_of_det_cc_upper
    {g : X → Y → α} {c : ℕ}
    (hMono : isMonoRectPartition Part g)
    (hFin : Part.Finite)
    (hc : Set.ncard Part ≤ 2 ^ c) :
    deterministic_communication_complexity (rectOf (isRectPartition_of_isMonoRectPartition hMono))
      ≤ (2 * (c + 1) ^ 2 : ℕ) :=
  det_cc_rectOf_le_sq_of_rect_partition
    (Part := Part)
    (hPart := isRectPartition_of_isMonoRectPartition hMono)
    (hFin := hFin)
    hc

end Theorem19

end DetProtocol
