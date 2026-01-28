import Mathlib


-- ## Painful examples

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

-- Can you understand the error message?
lemma quotComm_lemma {G : Type*} [Group G] (N : Subgroup G) : CommGroup (G ⧸ N) := by sorry

-- This is false, but at least it compiles
def quotComm_def {G : Type*} [Group G] (N : Subgroup G) : Group (G ⧸ N) := by sorry


lemma unit_surj (A B : Type*) [CommRing A] [CommRing B] {f : A →+* B} (a : Aˣ) : IsUnit (f a) := by
  rcases a with ⟨u, v, huv, hvu⟩
  rw [isUnit_iff_exists] -- very strange lemma
  refine ⟨f v, ?_, ?_⟩
  · simp [← map_mul, huv]
  · simp [← map_mul, hvu]

-- `⌘`

noncomputable section Groups

-- ### A wrong way to define structures

structure WrongGroup where
  carrier : Type*
  one : carrier
  mul : carrier → carrier → carrier
  inv : carrier → carrier
  mul_one : ∀ (x : carrier), mul x one = x
  one_mul : ∀ (x : carrier), mul one x = x
  mul_assoc : ∀ (x y z : carrier), mul (mul x y) z = mul x (mul y z)
  inv_mul_cancel : ∀ (x : carrier), mul (inv x) x = one

lemma WrongGroup.inv_eq_of_mul {α : WrongGroup} (x y : α.carrier) :
    α.mul x y = α.one → α.inv x = y := by
  intro h
  apply_fun (fun z ↦ α.mul (α.inv x) z) at h
      -- use the `apply_fun` tactic to apply a function to both sides of a hypothesis
  rw [α.mul_one, ← α.mul_assoc, α.inv_mul_cancel, α.one_mul] at h
  exact h.symm

structure WrongSemigroup where
  carrier : Type*
  mul : carrier → carrier → carrier
  mul_assoc : ∀ (x y z : carrier), mul (mul x y) z = mul x (mul y z)


lemma assoc_mul (X : WrongSemigroup) (x y z w : X.carrier) :
    X.mul x (X.mul (X.mul y z) w) = X.mul (X.mul x y) (X.mul z w) := by
  rw [X.mul_assoc]
  rw [X.mul_assoc]

lemma assoc_mul' (G : WrongGroup) (x y z w : G.carrier) :
    G.mul x (G.mul (G.mul y z) w) = G.mul (G.mul x y) (G.mul z w) := by
  -- apply assoc_mul -- it does not work!
  simp[G.mul_assoc]

def Nplus : WrongSemigroup where
  carrier := ℕ
  mul := (· + ·) -- or fun x y ↦ x + y
  mul_assoc := add_assoc

example : Nplus.mul (1 : ℕ) (1 : ℕ) = (2 : ℕ) := rfl
example : Nplus.mul 1 1 = 2 := rfl

-- `⌘`

-- ### A good way to define structures

#print Group
-- but right-clicking on it yields
structure Group_at_ENS (G : Type*) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

#print DivInvMonoid

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

#print CommGroup
-- but right-clicking on it yields
structure CommGroup_at_ENS (G : Type*) extends Group G, CommMonoid G

example {G : Type*} [CommGroup G] (x y : G) : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
  -- group
  rw [mul_inv_rev, mul_comm]
  -- rw [mul_inv]

example {A : Type*} [AddCommGroup A] (x y : A) : x + y + 0 = x + y := by
  abel

-- whatsnew in
-- @[to_additive]
lemma mul_square {G : Type*} [Group G] {x y : G} (h : x * y = 1) : x * y ^ 2 = y := by
  rw [pow_two]
  rw [← mul_assoc]
  rw [h]
  group

-- actually `mul_assoc` does not only work for groups.
#check mul_assoc

-- `⌘`

-- ## Classes

example {A : Type*} [AddGroup A] (x y : A) : x + y + 0 = x + y := by
  -- group
  simp

#print HAdd
-- @[inherit_doc] infixl:65 " + "   => HAdd.hAdd

#synth Group ℤ
#synth AddGroup ℤ
#synth AddGroup (ℤ × ℤ)

#print One
#synth One ℤ

example : AddGroup ℤ := inferInstance

example {A : Type*} [AddGroup A] {a b : A} (h : a + b = 0) : a + 2 • b = b := by
  -- exact add_even h
  rw [two_nsmul, ← add_assoc, h]
  simp

-- What's going on here?
example (G : Type*) [Group G] [CommGroup G] (g : G) : 1 * g = g := by
  rw [one_mul]

-- #### The `Coe` class
#check Complex.exp_add_pi_mul_I (3/2 : ℚ)

-- Anonymous function def!
instance : Coe WrongGroup Type where
  coe := (·.carrier)

-- instance : CoeSort WrongGroup Type where
--   coe := (·.carrier)


example {α : WrongGroup} (x : α) :
    α.mul x (α.inv x) = α.one := by
  rw [← α.inv_mul_cancel (α.inv x), α.inv_eq_of_mul _ _ (α.inv_mul_cancel x)]

-- instance : Add Bool where
--   add b₁ b₂ := b₁ && b₂

example : true + false = false := by rfl

-- `⌘`

-- ### More about groups

variable (G : Type*) [Group G]

-- #### Subgroups
example (H : Subgroup G) : Group H := inferInstance

variable (H : Subgroup G) in
#synth Group H

/- We have an automatic coercion from sets to types, so we get a coercion
from subgroups to types: -/
example (H : Subgroup G) (x : H) (hx : x = 1) : (x : G) = 1 := by
  simpa [OneMemClass.coe_eq_one]

example (H : Subgroup G) : 1 ∈ H := H.one_mem   -- elements of a subgroup


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

-- #### Quotients and homomorphisms

-- `simpa`
example (N : Subgroup G) [N.Normal] (x y : G) : (x : G ⧸ N) = (y : G ⧸ N) ↔ x * y⁻¹ ∈ N := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [QuotientGroup.eq] at h
    rw [← inv_inv x, ← mul_inv_rev]
    apply Subgroup.inv_mem
    rwa [Subgroup.Normal.mem_comm_iff]
    assumption
  · rw [QuotientGroup.eq, ← inv_inv y, ← mul_inv_rev]
    apply Subgroup.inv_mem
    simpa [Subgroup.Normal.mem_comm_iff]

@[ext]
structure MonoidHom_ENS (M N : Type*) [Monoid M] [Monoid N] where
-- We use the mathlib classes now.
  toFun : M → N
  map_one : toFun 1 = 1
  map_mul : ∀ (x y : M), toFun (x * y) = (toFun x) * (toFun y)

-- Note the @[ext] tag.
#check MonoidHom.ext

def f : MonoidHom_ENS (ℕ × ℕ) ℕ where
  toFun p := p.1 * p.2
  map_one := by simp only [Prod.fst_one, Prod.snd_one, mul_one]
  map_mul _ _ := by simp only [Prod.fst_mul, Prod.snd_mul]; group

#check f ⟨2,3⟩ -- we can't apply a `MonoidHom₁` to an element, which is annoying


#check f.toFun ⟨2,3⟩
#eval! f.toFun ⟨2,3⟩

/- We would like to able to write `f ⟨2,3⟩` instead of `f.toFun ⟨2,3⟩`. We do this
using the `CoeFun` class, which is a class for objects that can be coerced into
functions.-/

#print CoeFun

instance {G H : Type*} [Monoid G] [Monoid H] :
    CoeFun (MonoidHom_ENS G H) (fun _ ↦ G → H) where
  coe := MonoidHom_ENS.toFun

#check f ⟨2,3⟩

example (G₁ : Type) [CommGroup G₁] (f : G →* G₁) : ∀ x y : G, x * y = 1 → (f x) * (f y) = 1 := by
  intro x y h
  rw [← map_mul, h, map_one]

example (A : Type*) [AddGroup A] (f : G →* A) : ∀ x y : G, x * y = 1 → (f x) * (f y) = 1 := by sorry


open Function



/- Class type inference makes Lean understand that since `H` is
commutative, `N` is normal and thus `H ⧸ N` is a group. -/
example (H : Type*) [CommGroup H] (f : H →* G) (N : Subgroup H) (hN : N ≤ f.ker) :
    {g : H ⧸ N →* G // ∀ h : H, f h = g h } := by
  set g := QuotientGroup.lift N f hN with hg -- `set ... with`!
  use g
  intro h
  rw [hg]
  simp only [QuotientGroup.lift_mk]



example (A : Type*) [AddGroup A] (f : A →+ ℤ) (hf : 1 ∈ f.range) : Surjective f := by
  rcases hf with ⟨b, hb⟩
  intro m
  use m • b
  simp [map_zsmul, hb]


end Groups

section Rings

end Rings

noncomputable section Exercises

open Function

lemma WrongGroup.mul_inv_cancel {α : WrongGroup} (x : α.carrier) :
    α.mul x (α.inv x) = α.one := by
  rw [← α.inv_mul_cancel (α.inv x), α.inv_eq_of_mul _ _ (α.inv_mul_cancel x)]

/- ¶ Exercice
Why is the following example broken? Fix its statement, then prove it. -/
example (G : Type*) [Group G] (H₁ H₂ : Subgroup G) : Subgroup (H₁ ∩ H₂) := sorry


example (A B : Type*) [AddGroup A] [AddGroup B] (f : A →+ B) : Injective f ↔ f.ker = ⊥ := by
    -- (f.ker_eq_bot_iff).symm
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [AddSubgroup.eq_bot_iff_forall]
    intro x hx
    apply h
    rw [hx, map_zero]
  · rw [AddSubgroup.eq_bot_iff_forall] at h
    intro x y hxy
    rw [← sub_eq_zero] at hxy ⊢
    apply h (x - y)
    rwa [AddMonoidHom.mem_ker, map_sub]

-- Prove that the homomorphisms between commutative monoids have a structure of commutative monoid.
example (M N : Type*) [CommMonoid M] [CommMonoid N] : CommMonoid (M →* N) where
  mul := by
    intro f g
    fconstructor
    · use fun x ↦ f x * g x
      simp
    · intro x y
      simp [map_mul, mul_assoc _ (f y) _, mul_comm (f y) _, ← mul_assoc]
  mul_assoc := by
    intro f g h
    ext x
    simp only [MonoidHom.mul_apply]
    exact mul_assoc ..
  one := by
    fconstructor
    · use fun _ ↦ 1
    · intro x y
      simp
  one_mul := by simp
  mul_one := by simp
  mul_comm := by
    intro f g
    ext x
    simp only [MonoidHom.mul_apply]
    exact mul_comm ..

/- Prove that an injective and surjective group homomorphism is an isomorphism:
but what's an isomorphism? -/
def IsoOfBijective (G H : Type*) [Group G] [Group H] (f : G →* H)
    (h_surj : Surjective f) (h_inj : Injective f) : G ≃* H := by
  set g : G ≃ H := by
    apply Equiv.ofBijective f
    simp [Bijective, h_inj, h_surj] with hg
  use g
  intro x y
  simp [hg]

example (A : Type*) [AddCommGroup A] (N : AddSubgroup A) [N.Normal] (x y : A) :
    (x : A ⧸ N) = (y : A ⧸ N) ↔ y - x ∈ N := sorry

/- ¶ Exercice
Define the integers `ℤ` as a subgroup of the rationals `ℚ`: we'll see next time how to construct
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

/- ¶ Exercice
State and prove that every subgroup of a commutative group is normal: even if you find a one-line
proof, try to produce the whole term. -/
example (G : Type*) [CommGroup G] (H : Subgroup G) : H.Normal where
  conj_mem x hx g := by rwa [mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  -- infer_instance
  -- exact Subgroup.normal_of_comm H


/- ¶ Exercice
State and prove that in every additive group, the intersection of two normal subgroups is normal:
even if you find a one-line proof, try to produce the whole term. For reasons to be explained later,
the intersection is written `⊓` and types as `\inf`. -/
example (A : Type*) [AddGroup A] (H K : AddSubgroup A) :
    H.Normal → K.Normal → (H ⊓ K).Normal := by
  -- apply AddSubgroup.normal_inf_normal
  intro hH hK
  constructor
  rintro n ⟨hnH, hnK⟩ g
  exact ⟨hH.conj_mem n hnH g, hK.conj_mem n hnK g⟩


/- ¶ Exercice
State and that the kernel of every group homomorphism is normal: even if you find a one-line proof,
try to produce the whole term. -/
example (G G₁ : Type*) [Group G] [Group G₁] (f : G →* G₁) : (f.ker).Normal := by
  -- exact MonoidHom.normal_ker f
  -- infer_instance
  constructor
  intro x hy y
  simp only [f.mem_ker, map_mul, map_inv, conj_eq_one_iff]
  rwa [← f.mem_ker]

/- ¶ Exercice
State and that a group is commutative if and only if the map `x ↦ x⁻¹` is a group homomorphism:
even if you find a one-line proof, try to produce the whole term. To get `⁻¹`, type `\-1`. It can
be easier to split this `if and only if` statement in two declarations: are they both lemmas, both
definitions, a lemma and a definition?. -/
def inv_hom_of_comm (G : Type*) [CommGroup G] : G →* G where
  toFun := (·)⁻¹
  map_one' := by simp
  map_mul' x y := by
    simp [← mul_inv_rev, mul_comm]

def comm_of_inv_hom (G : Type*) [Group G] (f : G →* G) (hf : ∀ x, f x = x⁻¹) :
    CommGroup G where
  mul_comm g h := by
    have h1 := hf (g * h)
    rwa [mul_inv_rev, map_mul, hf, hf, inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq,
      eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul] at h1


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
