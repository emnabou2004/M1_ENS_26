import Mathlib

section Groups

variable {G : Type*} [Group G]

example (g e : G) (h : g * e = g) : e = 1 := by
  calc e = 1 * e := by rw [one_mul]
      _ = g⁻¹ * g * e := by rw [← inv_mul_cancel]
      _ = g⁻¹ * (g * e) := by rw [mul_assoc]
      _ = g⁻¹ * g := by rw [h]
      _ = 1 := by rw [inv_mul_cancel]
  -- rw [← left_eq_mul, h]

@[to_additive]
instance [IsCyclic G] (N : Subgroup G) : N.Normal :=
    @N.normal_of_comm _ IsCyclic.commGroup

@[to_additive]
theorem isCyclic_quotient [IsCyclic G] (N : Subgroup G) : IsCyclic (G ⧸ N) :=
    isCyclic_of_surjective _ <| QuotientGroup.mk'_surjective _


end Groups
