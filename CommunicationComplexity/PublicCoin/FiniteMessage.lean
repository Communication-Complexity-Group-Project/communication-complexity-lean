import CommunicationComplexity.PublicCoin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.MeasurableSpace.Defs

namespace CommunicationComplexity

/-- A public-coin two-party communication protocol where at each step,
a player sends an element of an arbitrary finite type `β`.
Both players share the same `CoinTape n`.
Sending a `β`-valued message costs `⌈log₂ |β|⌉` bits. -/
inductive PublicCoin.FiniteMessage.Protocol
    (n : ℕ) (X Y α : Type*) where
  | output (a : α) :
      PublicCoin.FiniteMessage.Protocol n X Y α
  | alice {β : Type} [Fintype β] [Nonempty β]
      (f : X → CoinTape n → β)
      (P : β → PublicCoin.FiniteMessage.Protocol n X Y α) :
      PublicCoin.FiniteMessage.Protocol n X Y α
  | bob {β : Type} [Fintype β] [Nonempty β]
      (f : Y → CoinTape n → β)
      (P : β → PublicCoin.FiniteMessage.Protocol n X Y α) :
      PublicCoin.FiniteMessage.Protocol n X Y α

namespace PublicCoin.FiniteMessage.Protocol

variable {n : ℕ} {X Y α : Type*}

/-- Executes the public-coin finite-message protocol on inputs `x`, `y`
with shared coin flips `ω`. -/
def run (p : Protocol n X Y α)
    (x : X) (y : Y) (ω : CoinTape n) : α :=
  match p with
  | output a => a
  | alice f P => (P (f x ω)).run x y ω
  | bob f P => (P (f y ω)).run x y ω

/-- The communication complexity of a public-coin finite-message protocol.
Sending a `β`-valued message costs `⌈log₂ |β|⌉` bits. -/
def complexity : Protocol n X Y α → ℕ
  | output _ => 0
  | alice (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)
  | bob (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)

/-- Swaps the roles of Alice and Bob. -/
def swap : Protocol n X Y α → Protocol n Y X α
  | .output a => .output a
  | alice f P =>
      bob f (fun b => (P b).swap)
  | bob f P =>
      alice f (fun b => (P b).swap)

@[simp]
theorem swap_run (p : Protocol n X Y α) (x : X) (y : Y)
    (ω : CoinTape n) :
    p.swap.run y x ω = p.run x y ω := by
  induction p with
  | output a => simp [swap, run]
  | alice f P ih => simp only [swap, run]; exact ih _
  | bob f P ih => simp only [swap, run]; exact ih _

@[simp]
theorem swap_complexity (p : Protocol n X Y α) :
    p.swap.complexity = p.complexity := by
  induction p with
  | output a => simp [swap, complexity]
  | alice f P ih => simp only [swap, complexity, ih]
  | bob f P ih => simp only [swap, complexity, ih]

/-- Embed a binary public-coin protocol into a finite-message
public-coin protocol (with `β = Bool` at each step). -/
def ofProtocol :
    PublicCoin.Protocol n X Y α →
      Protocol n X Y α
  | PublicCoin.Protocol.output a => output a
  | PublicCoin.Protocol.alice f P =>
      alice f (fun b => ofProtocol (P b))
  | PublicCoin.Protocol.bob f P =>
      bob f (fun b => ofProtocol (P b))

theorem ofProtocol_run
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

theorem ofProtocol_complexity
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

/-- Every binary public-coin protocol can be viewed as a finite-message
public-coin protocol with the same run behavior and complexity. -/
theorem ofProtocol_equiv
    (p : PublicCoin.Protocol n X Y α) :
    ∃ (P : Protocol n X Y α),
      P.run = p.run ∧ P.complexity = p.complexity :=
  ⟨ofProtocol p,
   funext₂ fun x y => funext fun ω =>
     ofProtocol_run p x y ω,
   ofProtocol_complexity p⟩

open MeasureTheory

/-- A public-coin finite-message protocol `ε`-satisfies a predicate `Q`
if for every input `(x, y)`, the probability that
`Q x y (p.run ...)` fails is at most `ε`. -/
def approx_satisfies
    (p : Protocol n X Y α) (Q : X → Y → α → Prop)
    (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : CoinTape n |
      ¬Q x y (p.run x y ω)}).toReal ≤ ε

open Classical in
/-- A public-coin finite-message protocol `ε`-computes a function `f`
if for every input `(x, y)`, the probability of producing an
incorrect answer is at most `ε`. -/
def approx_computes
    (p : Protocol n X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : CoinTape n |
      p.run x y ω ≠ f x y}).toReal ≤ ε

end PublicCoin.FiniteMessage.Protocol

end CommunicationComplexity
