import CommunicationComplexity.PublicCoin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory

namespace CommunicationComplexity

/-- A public-coin two-party communication protocol where at each step,
a player sends an element of an arbitrary finite type `β`.
This version uses an arbitrary finite probability space `Ω` shared
by both players. Sending a `β`-valued message costs `⌈log₂ |β|⌉` bits.

Since `Ω` is finite, all functions out of it are automatically
measurable, so no measurability hypotheses are needed. -/
inductive PublicCoin.GeneralFiniteMessage.Protocol
    (Ω : Type*) [Fintype Ω]
    (X Y α : Type*) where
  | output (a : α) :
      PublicCoin.GeneralFiniteMessage.Protocol Ω X Y α
  | alice {β : Type} [Fintype β] [Nonempty β]
      (f : X → Ω → β)
      (P : β → PublicCoin.GeneralFiniteMessage.Protocol Ω X Y α) :
      PublicCoin.GeneralFiniteMessage.Protocol Ω X Y α
  | bob {β : Type} [Fintype β] [Nonempty β]
      (f : Y → Ω → β)
      (P : β → PublicCoin.GeneralFiniteMessage.Protocol Ω X Y α) :
      PublicCoin.GeneralFiniteMessage.Protocol Ω X Y α

namespace PublicCoin.GeneralFiniteMessage.Protocol

variable {Ω X Y α : Type*} [Fintype Ω]

/-- Executes the public-coin generalized protocol on inputs `x`, `y`
with shared randomness `ω`. -/
def run (p : Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω) : α :=
  match p with
  | output a => a
  | alice f P => (P (f x ω)).run x y ω
  | bob f P => (P (f y ω)).run x y ω

/-- The communication complexity of a public-coin generalized protocol.
Sending a `β`-valued message costs `⌈log₂ |β|⌉` bits. -/
def complexity : Protocol Ω X Y α → ℕ
  | output _ => 0
  | alice (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)
  | bob (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)

/-- Swaps the roles of Alice and Bob. The shared randomness
is unchanged. -/
def swap : Protocol Ω X Y α → Protocol Ω Y X α
  | .output a => .output a
  | alice f P =>
      bob f (fun b => (P b).swap)
  | bob f P =>
      alice f (fun b => (P b).swap)

@[simp]
theorem swap_run (p : Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω) :
    p.swap.run y x ω = p.run x y ω := by
  induction p with
  | output a => simp [swap, run]
  | alice f P ih => simp only [swap, run]; exact ih _
  | bob f P ih => simp only [swap, run]; exact ih _

@[simp]
theorem swap_complexity (p : Protocol Ω X Y α) :
    p.swap.complexity = p.complexity := by
  induction p with
  | output a => simp [swap, complexity]
  | alice f P ih => simp only [swap, complexity, ih]
  | bob f P ih => simp only [swap, complexity, ih]

/-- The preimage of any set under the protocol's output is measurable.
Since `Ω` is finite, it has discrete measurable space, so every
set is measurable. -/
theorem measurable_preimage_run
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (p : Protocol Ω X Y α) (x : X) (y : Y) (s : Set α) :
    MeasurableSet ((fun ω ↦ p.run x y ω) ⁻¹' s) :=
  MeasurableSet.of_discrete

/-- Embed a coin-flip public-coin protocol into a generalized
public-coin protocol over `CoinTape` (with `β = Bool`
at each step). -/
def ofProtocol {n : ℕ} :
    PublicCoin.Protocol n X Y α →
      Protocol (CoinTape n) X Y α
  | PublicCoin.Protocol.output a => output a
  | PublicCoin.Protocol.alice f P =>
      alice f (fun b => ofProtocol (P b))
  | PublicCoin.Protocol.bob f P =>
      bob f (fun b => ofProtocol (P b))

theorem ofProtocol_run {n : ℕ}
    (p : PublicCoin.Protocol n X Y α)
    (x : X) (y : Y) (ω : CoinTape n) :
    (ofProtocol p).run x y ω =
      p.run x y ω := by
  induction p with
  | output a =>
    simp [ofProtocol, run, PublicCoin.Protocol.run]
  | alice f P ih =>
    simp [ofProtocol, run, PublicCoin.Protocol.run, ih]
  | bob f P ih =>
    simp [ofProtocol, run, PublicCoin.Protocol.run, ih]

theorem ofProtocol_complexity {n : ℕ}
    (p : PublicCoin.Protocol n X Y α) :
    (ofProtocol p).complexity = p.complexity := by
  induction p with
  | output a =>
    simp [ofProtocol, complexity,
      PublicCoin.Protocol.complexity]
  | alice f P ih =>
    simp only [ofProtocol, complexity,
      PublicCoin.Protocol.complexity, ih]
    have : Nat.clog 2 (Fintype.card Bool) = 1 := by decide
    rw [this]
    have : (Finset.univ : Finset Bool) = {false, true} := by
      ext b; simp
    simp [this]
  | bob f P ih =>
    simp only [ofProtocol, complexity,
      PublicCoin.Protocol.complexity, ih]
    have : Nat.clog 2 (Fintype.card Bool) = 1 := by decide
    rw [this]
    have : (Finset.univ : Finset Bool) = {false, true} := by
      ext b; simp
    simp [this]

/-- Every coin-flip public-coin protocol can be viewed as a generalized
public-coin protocol with the same run behavior and complexity. -/
theorem ofProtocol_equiv {n : ℕ}
    (p : PublicCoin.Protocol n X Y α) :
    ∃ (P : Protocol (CoinTape n) X Y α),
      P.run = p.run ∧ P.complexity = p.complexity :=
  ⟨ofProtocol p,
   funext₂ fun x y => funext fun ω =>
     ofProtocol_run p x y ω,
   ofProtocol_complexity p⟩

end PublicCoin.GeneralFiniteMessage.Protocol

end CommunicationComplexity
