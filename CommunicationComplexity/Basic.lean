import Mathlib

open MeasureTheory ProbabilityTheory

inductive DetProtocol (X Y α : Type*) where
  | result (val : α) : DetProtocol X Y α
  | alice (f : X → Bool) (P0 : DetProtocol X Y α) (P1 : DetProtocol X Y α) : DetProtocol X Y α
  | bob (f : Y → Bool) (P0 : DetProtocol X Y α) (P1 : DetProtocol X Y α) : DetProtocol X Y α

namespace DetProtocol

def run {X Y α : Type*} (p : DetProtocol X Y α) (x : X) (y : Y) : α :=
  match p with
  | DetProtocol.result val => val
  | DetProtocol.alice f P0 P1 => if f x then P1.run x y else P0.run x y
  | DetProtocol.bob f P0 P1 => if f y then P1.run x y else P0.run x y

def complexity {X Y α : Type*} : DetProtocol X Y α → ℕ
  | DetProtocol.result _ => 0
  | DetProtocol.alice _ P0 P1 => 1 + max P0.complexity P1.complexity
  | DetProtocol.bob _ P0 P1 => 1 + max P0.complexity P1.complexity

def equiv {X Y α : Type*} (p q : DetProtocol X Y α) : Prop :=
  ∀ x y, p.run x y = q.run x y

end DetProtocol

inductive RandProtocol
    (Ω_X Ω_Y : Type*)
    [MeasurableSpace Ω_X] [MeasurableSpace Ω_Y]
    (μ_X : ProbabilityMeasure Ω_X)
    (μ_Y : ProbabilityMeasure Ω_Y)
    (X Y α : Type*) where
  | output (a : α) :
      RandProtocol Ω_X Ω_Y μ_X μ_Y X Y α
  | alice
      (f : X → Ω_X → Bool)
      (hf : ∀ x, Measurable (f x))
      (P0 P1 : RandProtocol Ω_X Ω_Y μ_X μ_Y X Y α) :
      RandProtocol Ω_X Ω_Y μ_X μ_Y X Y α
  | bob
      (f : Y → Ω_Y → Bool)
      (hf : ∀ y, Measurable (f y))
      (P0 P1 : RandProtocol Ω_X Ω_Y μ_X μ_Y X Y α) :
      RandProtocol Ω_X Ω_Y μ_X μ_Y X Y α
