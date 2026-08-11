theorem verifier_smoke (left right : Nat) : left + right = right + left := by
  exact Nat.add_comm left right
