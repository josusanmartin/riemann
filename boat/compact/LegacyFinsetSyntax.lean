import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

-- The winner was authored against the two-premise, nonnegative-product lemma.
-- Mathlib 4.35 gives that exact lemma the suffixed name.
macro "Finset.prod_le_prod" : term => `(_root_.Finset.prod_le_prod₀)
