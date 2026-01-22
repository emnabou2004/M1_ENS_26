import Mathlib

section Groups

-- ## Bad Ideas

example {G : Type*} [Group G] (g e : G) (h : g * e = g) : e = 1 := by
  calc e = 1 * e := by rw [one_mul]
      _ = g⁻¹ * g * e := by rw [← inv_mul_cancel]
      _ = g⁻¹ * (g * e) := by rw [mul_assoc]
      _ = g⁻¹ * g := by rw [h]
      _ = 1 := by rw [inv_mul_cancel]
  -- rw [← left_eq_mul, h]

example {G : Type*} [CommGroup G] (N : Subgroup G) : CommGroup (G ⧸ N) := by
  constructor
  rintro a b
  obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective N a
  obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective N b
  rw [← ha', ← hb'/- , QuotientGroup.mk'_apply, QuotientGroup.mk'_apply-/]
  simp only [QuotientGroup.mk'_apply]
  apply CommGroup.mul_comm
  -- exact QuotientGroup.Quotient.commGroup N

lemma quotComm_lemma {G : Type*} [Group G] (N : Subgroup G) : CommGroup (G ⧸ N) := by sorry

def quotComm_def {G : Type*} [Group G] (N : Subgroup G) : CommGroup (G ⧸ N) := by sorry

lemma unit_surj (A B : Type*) [CommRing A] [CommRing B] {f : A →+* B} (a : Aˣ) : IsUnit (f a) := by
  rcases a with ⟨u, v, huv, hvu⟩
  rw [isUnit_iff_exists]
  refine ⟨f v, ?_, ?_⟩
  · simp [← map_mul, huv]
  · simp [← map_mul, hvu]

-- `⌘`

-- ## Basic facts about groups

-- ### Definitions, basic properties and some tactics
structure WrongGroup where
  carrier : Type _
  one : carrier
  mul : carrier → carrier → carrier
  inv : carrier → carrier
  mul_one : ∀ (x : carrier), mul x one = x
  one_mul : ∀ (x : carrier), mul one x = x
  mul_assoc : ∀ (x y z : carrier), mul (mul x y) z = mul x (mul y z)
  inv_mul_cancel : ∀ (x : carrier), mul (inv x) x = one
-- You might want to put one more condition called `mul_inv_cancel`, but we can
-- actually prove it from the others.


lemma WrongGroup.inv_eq_of_mul {α : WrongGroup} (x y : α.carrier) :
    α.mul x y = α.one → α.inv x = y := by
  intro h
  apply_fun (fun z ↦ α.mul (α.inv x) z) at h
      -- use the `apply_fun` tactic to apply a function to both sides of a hypothesis
  rw [α.mul_one, ← α.mul_assoc, α.inv_mul_cancel, α.one_mul] at h
  exact h.symm

lemma WrongGroup.mul_inv_cancel {α : WrongGroup} (x : α.carrier) :
    α.mul x (α.inv x) = α.one := by
  rw [← α.inv_mul_cancel (α.inv x), α.inv_eq_of_mul _ _ (α.inv_mul_cancel x)]

#print Group
-- class Group (G : Type*) extends DivInvMonoid G where
--   protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

#print DivInvMonoid

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

example {G : Type*} [CommGroup G] (x y : G) : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
  -- group
  rw [mul_inv_rev, mul_comm]
  -- rw [mul_inv]

example {A : Type*} [AddGroup A] (x y : A) : x + y + 0 = x + y := by
  -- group
  simp

example {A : Type*} [AddCommGroup A] (x y : A) : x + y + 0 = x + y := by
  abel


#check mul_assoc
-- whatsnew in
-- @[to_additive]
lemma mul_square {G : Type*} [Group G] {x y : G} (h : x * y = 1) : x * y ^ 2 = y := by
  rw [pow_two]
  rw [← mul_assoc]
  rw [h]
  group

example {A : Type*} [AddGroup A] {a b : A} (h : a + b = 0) : a + 2 • b = b := by
  -- exact add_even h
  rw [two_nsmul, ← add_assoc, h]
  simp

-- `⌘`

-- ## Classes

-- What's going on here?!?!
example (G : Type*) [Group G] [CommGroup G] (g : G) : 1 * g = g := by
  rw [one_mul]

instance : CoeSort WrongGroup (Type) where
  coe := (·.carrier)

-- Anonymous function def!
instance : Coe WrongGroup (Type ) where
  coe := (·.carrier)

example {α : WrongGroup} (x : α) :
    α.mul x (α.inv x) = α.one := by
  rw [← α.inv_mul_cancel (α.inv x), α.inv_eq_of_mul _ _ (α.inv_mul_cancel x)]



-- ### More about groups

variable (G : Type*) [Group G]

/- Now for the group structure on subgroups.

We have an automatic coercion from sets to types, so we get a coercion
from subgroups to types:
-/


example (H : Subgroup G) : 1 ∈ H := H.one_mem   -- elements of a subgroup

-- This looks stupid but it is not!
example (H : Subgroup G) (x : H) : (1 : G) = (1 : H) := by sorry
  -- set x' : G := x.1
  -- set x'' : G := x.val
  -- set x''' : G := (x : G)
  -- have xprop := x.2
  -- have xprop' := x.property
  -- rfl

-- What happens if one writes `AddSubgroup ℤ`? And how can we populate the fields automatically?
example : AddSubgroup ℤ where
  carrier := {n : ℤ | Even n}
  add_mem' := by
    intro a b ha hb
    -- simp at ha hb --not needed, actually
    simp only [Even] at ha hb
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    rw [hn, hm]
    use n + m
    abel
    -- grind
  zero_mem' := ⟨0, by abel⟩
  neg_mem' {x} hx := by
    obtain ⟨r, _⟩ := hx
    exact ⟨-r, by simp_all⟩

---dot notation!
example : (Subgroup.center G).Normal := by
-- #print Subgroup.Normal
  apply Subgroup.Normal.mk
  intro z hz g
  let hz' := hz
  rw [Subgroup.mem_center_iff] at hz --this looses hz
  specialize hz g
  rw [← mul_inv_eq_iff_eq_mul] at hz
  rwa [hz]
  -- exact Subgroup.instNormalCenter

-- `⌘`

-- `simpa`
example (N : Subgroup G) [N.Normal] (x y : G) : (x : G ⧸ N) = (y : G ⧸ N) ↔ x * y⁻¹ ∈ N := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [QuotientGroup.eq] at h
    rw [← inv_inv x, ← mul_inv_rev]
    apply Subgroup.inv_mem
    rw [Subgroup.Normal.mem_comm_iff]
    exact h
    assumption
  · rw [QuotientGroup.eq, ← inv_inv y, ← mul_inv_rev]
    apply Subgroup.inv_mem
    simpa [Subgroup.Normal.mem_comm_iff]



-- ### Group homomorphisms
@[ext]
structure MonoidHom₁ (M N : Type*) [Monoid M] [Monoid N] where
-- We use the mathlib classes now.
  toFun : M → N
  map_one : toFun 1 = 1
  map_mul : ∀ (x y : M), toFun (x * y) = (toFun x) * (toFun y)

-- Not the @[ext] tag.
#check MonoidHom₁.ext

def f : MonoidHom₁ (ℕ × ℕ) ℕ where
  toFun p := p.1 * p.2
  map_one := by simp only [Prod.fst_one, Prod.snd_one, mul_one]
  map_mul p p' := by simp only [Prod.fst_mul, Prod.snd_mul]; ring

/-
#check f ⟨2,3⟩ -- we can't apply a `MonoidHom₁` to an element, which is annoying
-/

#check f.toFun ⟨2,3⟩
#eval! f.toFun ⟨2,3⟩

/- We would like to able to write `f ⟨2,3⟩` instead of `f.toFun ⟨2,3⟩`. We do this
using the `CoeFun` class, which is a class for objects that can be coerced into
functions.-/

#print CoeFun

instance {G H : Type*} [Monoid G] [Monoid H] :
    CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

#check f ⟨2,3⟩



end Groups

section Rings

end Rings

section Exercises

-- Why is the following example broken? Fix its statement, then prove it.
example (G : Type*) [Group G] (H₁ H₂ : Subgroup G) : Subgroup (H₁ ∩ H₂) := sorry


example (A : Type*) [AddCommGroup A] (N : AddSubgroup A) [N.Normal] (x y : A) :
    (x : A ⧸ N) = (y : A ⧸ N) ↔ y - x ∈ N := sorry

/- Define the integers `ℤ` as a subgroup of the rationals `ℚ`: we'll see next time how to construct
(sub)sets, for the time being use `Set.range ((↑) : ℤ → ℚ)` , by copy-pasting it, as carrier. -/
example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp



end Exercises
section Later

open Ideal in
-- **FAE** Use later
theorem idealProd (A B : Type*) [CommRing A] [CommRing B] (J : Ideal (A × B)) :
    ∃ P : Ideal A × Ideal B, J = Ideal.prod P.1 P.2 := by
  set Ia := J.map <| RingHom.fst .. with hIa
  set Ib := J.map <| RingHom.snd .. with hIb
  use ⟨Ia, Ib⟩
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · constructor
    · apply Ideal.mem_map_of_mem
      exact hx
    · apply Ideal.mem_map_of_mem
      exact hx
  · rw [mem_prod, mem_map_iff_of_surjective _ (RingHomSurjective.is_surjective),
        mem_map_iff_of_surjective _ (RingHomSurjective.is_surjective)] at hx
    obtain ⟨⟨y, hy_mem, hyx⟩, ⟨z, hz_mem, hzx⟩⟩ := hx
    have : ⟨x.1, 0⟩ + ⟨0, x.2⟩ = x := Prod.fst_add_snd x
    rw [← this, ← hyx, ← hzx]
    simp only [RingHom.coe_fst, RingHom.coe_snd, Prod.mk_add_mk, add_zero, zero_add]
    replace hyx : ⟨y.1, y.2⟩ * ⟨1, 0⟩ = (⟨y.1, 0⟩ : A × B) := by
        calc ⟨y.1, y.2⟩ * ⟨1, 0⟩ = ⟨y.1 * 1, y.2 * 0⟩ := by rfl
                               _ = (⟨y.1, 0⟩ : A × B) := by rw [mul_one, mul_zero]
    replace hzx : ⟨z.1, z.2⟩ * ⟨0, 1⟩ = (⟨0, z.2⟩ : A × B) := by
        calc ⟨z.1, z.2⟩ * ⟨0, 1⟩ = ⟨z.1 * 0, z.2 * 1⟩ := by rfl
                                 _ = (⟨0, z.2⟩ : A × B) := by rw [mul_one, mul_zero]
    rw [← zero_add y.1, ← add_zero z.2, ← Prod.mk_add_mk 0 y.1 z.2 0, ← hzx, ← hyx, Prod.mk.eta,
        Prod.mk.eta]
    apply J.add_mem (J.mul_mem_right _ hz_mem) (J.mul_mem_right _ hy_mem)


open Ideal in
-- **FAE** Use later
theorem idealProd' (A B : Type*) [CommRing A] [CommRing B] (J : Ideal (A × B)) :
    ∃ P : Ideal A × Ideal B, J = Ideal.prod P.1 P.2 :=
  ⟨⟨J.map <| RingHom.fst .., J.map <| RingHom.snd ..⟩, J.ideal_prod_eq⟩

-- def idealProd (A B : Type*) [CommRing A] [CommRing B] (J : Ideal A × B) : (Ideal A) x (Ideal B) := by

-- @[to_additive]
-- instance [IsCyclic G] (N : Subgroup G) : N.Normal :=
--     @N.normal_of_comm _ IsCyclic.commGroup
--
-- @[to_additive]
-- theorem isCyclic_quotient [IsCyclic G] (N : Subgroup G) : IsCyclic (G ⧸ N) :=
--     isCyclic_of_surjective _ <| QuotientGroup.mk'_surjective _

end Later
