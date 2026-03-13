import CommunicationComplexity.Basic
import CommunicationComplexity.UpperBounds.Basic

/-- The equality function on `n`-bit strings. Returns `true` iff the two inputs are equal. -/
def EQ (n : ℕ) (x y : Fin n → Bool) : Bool :=
  decide (x = y)

/-- The deterministic communication complexity of EQ is at most n + 1:
Alice sends her n-bit input, Bob computes equality and sends one bit. -/
theorem det_cc_EQ_le (n : ℕ) :
    deterministic_communication_complexity (EQ n) ≤ n + 1 := by
  calc deterministic_communication_complexity (EQ n)
      ≤ Nat.clog 2 (Fintype.card (Fin n → Bool)) + Nat.clog 2 (Fintype.card Bool) :=
        det_cc_le_clog_card_X_alpha (EQ n)
    _ = n + 1 := by
        simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, Nat.one_lt_ofNat, Nat.clog_pow, ne_eq, WithTop.natCast_ne_top,
          not_false_eq_true, add_right_inj_of_ne_top, Nat.cast_eq_one]
        decide
