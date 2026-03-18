import CommunicationComplexity.PublicCoin.GeneralFiniteMessage

namespace CommunicationComplexity

namespace PublicCoin.GeneralFiniteMessage.Protocol

variable {Ω Ω₁ Ω₂ X Y α α₁ α₂ β : Type*}

/-- Map a function over the output of a protocol. -/
def map [Fintype Ω] (g : α → β) :
    Protocol Ω X Y α → Protocol Ω X Y β
  | .output a => .output (g a)
  | alice f P =>
      alice f (fun b => (P b).map g)
  | bob f P =>
      bob f (fun b => (P b).map g)

@[simp]
theorem map_run [Fintype Ω] (g : α → β)
    (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) :
    (p.map g).run x y ω = g (p.run x y ω) := by
  induction p with
  | output a => simp [map, run]
  | alice f P ih => simp only [map, run]; exact ih _
  | bob f P ih => simp only [map, run]; exact ih _

@[simp]
theorem map_complexity [Fintype Ω] (g : α → β)
    (p : Protocol Ω X Y α) :
    (p.map g).complexity = p.complexity := by
  induction p with
  | output a => simp [map, complexity]
  | alice f P ih => simp only [map, complexity, ih]
  | bob f P ih => simp only [map, complexity, ih]

variable {Ω' : Type*}

/-- Reindex the randomness space of a protocol via a map `h : Ω' → Ω`. -/
def comapRandomness [Fintype Ω] [Fintype Ω'] (h : Ω' → Ω) :
    Protocol Ω X Y α → Protocol Ω' X Y α
  | .output a => .output a
  | alice f P =>
      alice (fun x ω => f x (h ω))
        (fun b => (P b).comapRandomness h)
  | bob f P =>
      bob (fun y ω => f y (h ω))
        (fun b => (P b).comapRandomness h)

@[simp]
theorem comapRandomness_run [Fintype Ω] [Fintype Ω']
    (h : Ω' → Ω) (p : Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω') :
    (p.comapRandomness h).run x y ω = p.run x y (h ω) := by
  induction p with
  | output a => simp [comapRandomness, run]
  | alice f P ih => simp only [comapRandomness, run]; exact ih _
  | bob f P ih => simp only [comapRandomness, run]; exact ih _

@[simp]
theorem comapRandomness_complexity [Fintype Ω] [Fintype Ω']
    (h : Ω' → Ω) (p : Protocol Ω X Y α) :
    (p.comapRandomness h).complexity = p.complexity := by
  induction p with
  | output a => simp [comapRandomness, complexity]
  | alice f P ih => simp only [comapRandomness, complexity, ih]
  | bob f P ih => simp only [comapRandomness, complexity, ih]

variable [Fintype Ω₁] [Fintype Ω₂]

/-- Oblivious composition of two public-coin protocols. Runs `p1` using
the first component of `Ω₁ × Ω₂`, then `p2` using the second, and
pairs their outputs. The total complexity is the sum. -/
def obliviousCompose
    (p1 : Protocol Ω₁ X Y α₁) (p2 : Protocol Ω₂ X Y α₂) :
    Protocol (Ω₁ × Ω₂) X Y (α₁ × α₂) :=
  match p1 with
  | .output a1 =>
      (p2.comapRandomness Prod.snd).map (fun a2 => (a1, a2))
  | alice f P =>
      alice (fun x ω => f x ω.1)
        (fun b => (P b).obliviousCompose p2)
  | bob f P =>
      bob (fun y ω => f y ω.1)
        (fun b => (P b).obliviousCompose p2)

@[simp]
theorem obliviousCompose_run
    (p1 : Protocol Ω₁ X Y α₁) (p2 : Protocol Ω₂ X Y α₂)
    (x : X) (y : Y) (ω : Ω₁ × Ω₂) :
    (p1.obliviousCompose p2).run x y ω =
      (p1.run x y ω.1, p2.run x y ω.2) := by
  induction p1 with
  | output a1 => simp [obliviousCompose, run]
  | alice f P ih => simp only [obliviousCompose, run]; exact ih _
  | bob f P ih => simp only [obliviousCompose, run]; exact ih _

private theorem finset_sup_add_const {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℕ) (c : ℕ) :
    Finset.univ.sup (fun i => f i + c) =
      Finset.univ.sup f + c := by
  apply le_antisymm
  · apply Finset.sup_le; intro i _
    exact Nat.add_le_add (Finset.le_sup (Finset.mem_univ i)) le_rfl
  · have ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty f
    rw [hj]
    exact Finset.le_sup (f := fun i => f i + c) (Finset.mem_univ j)

theorem obliviousCompose_complexity
    (p1 : Protocol Ω₁ X Y α₁) (p2 : Protocol Ω₂ X Y α₂) :
    (p1.obliviousCompose p2).complexity =
      p1.complexity + p2.complexity := by
  induction p1 with
  | output a1 => simp [obliviousCompose, complexity]
  | alice f P ih =>
    simp only [obliviousCompose, complexity, ih]
    rw [finset_sup_add_const]; omega
  | bob f P ih =>
    simp only [obliviousCompose, complexity, ih]
    rw [finset_sup_add_const]; omega

end PublicCoin.GeneralFiniteMessage.Protocol

end CommunicationComplexity
