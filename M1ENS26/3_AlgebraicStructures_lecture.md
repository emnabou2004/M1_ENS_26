# Algebraic Structures

Let's begin with some *painful* example: `⌘`

They show that algebraic manipulations "from first principles" are doable, but certainly the *wrong* way to go.

## Groups
In this section we're going to see 
1. A bad definition of (the right notion of) group;
1. A complicated one of the same notion, adapted for formalisation — and its advantages; 
1. How to benefit from Mathlib, a huge library where all this has already been defined.

`⌘`

The problems with `WrongGroup` and `WrongSemigroup` are (among others...)
* We're carrying around `mul`, `one` and `inv`, together with the type: `α.one` or `X.mul` or `G.inv`...
* Math is full of hierarchies, and these are not respected: but we don't want to re-prove a theorem on additive commutative groups for rings, then for commutative rings, then for integral domains, then for fields...
* Although we can create 
```
def Nplus : WrongSemigroup where
  carrier := ℕ
  mul := (· + ·) -- or fun x y ↦ x + y
  mul_assoc := add_assoc
```
it is unhandy to connect `Nplus` with `ℕ` *as types*.

#### Extends

The right approach relies on the idea of *extending* structures. 

Suppose we've already defined a structure `PoorStructure` with fields `firstfield,...,nth_field` and  we want a new *richer* structure `RichStructure` that also contains the fields
`(n+1)st_field,...,rth_field`. We can either

* forget that we had `PoorStructure` and declare
  ```  
  structure RichStructure where
    firstfield : firstType
    secondfield : secondType
    ...
    rth_field : rth_Type
  ```

* declare that `RichStructure` extends `PoorStructure` inheriting terms from the latter:

  ```
  structure RichStructure extends PoorStructure where
      (n+1)st_field : (n+1)st_Type
      ...
      rth_field : rth_Type
  ```

+++ In details (to be read at home...)
* The process can be iterated, yielding a structure extending several ones:

        VeryRichStructure extends Structure₁, Structure₂, Structure₃ where
            ...

* If the parent structures have overlapping field names, then all overlapping field names 
must have the **same type**. 
* If the overlapping fields have different default values, then the default value 
from the **last** parent structure that includes the field is used. New default values in the child
(= richer) structure take precedence over default values from the parent (= poorer) structures.

* The `with` (and `__`) syntax are able to "read through" the extension of structures.
+++

`⌘`

### Classes and Class Inference
+++ Some automation we’ve just witnessed
1. Lean was able to "automatically" decide to use `1` and `*` for `G : Group` or `G : CommGroup`,
and to use `0` and `+` for `A : AddGroup` or `A : AddCommGroup`.
1. If we inspect `mul_assoc` we see
    ```
    mul_assoc {G : Type*} [Semigroup G] (a b c : G) : a * b * c = a * (b * c)
    ```
but we used it for a group: Lean understood that every group is a semigroup.
1. The use of `extend` to define `Group`, yielding an "enriched" `DivInvMonoid`.
1. Some redundancy in the definition of `Group` (of `Monoid`, actually) concerning `npow : ℕ → M → M`.
+++
Most of the above points are related to *classes* and *class type inference*.

1. Discuss what classes are, what inference is, what `[` and `]` are, what instances are
1. Discuss `#synth` 
1. Make examples of instances: beyond notation, start with `Coe` (and `CoeSort`); then go back to "every group is a monoid" and the quotcommlemma.
### More about groups

+++ Interlude: `Mathlib`
#### Main take-home message: it is huge!

You can access it on its [gitHub repo](https://github.com/leanprover-community/mathlib4) or, **much better**, through its [documentation website](https://leanprover-community.github.io/mathlib4_docs/). It changes very rapidly (>10 times a day), so I created a ["frozen" documentation](https://faenuccio-teaching.github.io/M1_ENS_26/docs/) website with the Mathlib version used in this course.

As a rule of thumb: 
* if something is below PhD level it is *probably* in Mathlib. Unless it is not.
* Generality is normally overwhelming, so if you don't find something you're probably looking in the wrong place.
* There is a naming convention for theorems (terms of `Prop`-valued types), for objects (terms in `Type*`), for properties (terms in `Prop`); together with plenty of exceptions and room for headache. Try to develop your feeling and ask for help. 
+++
#### Subgroups
The definition of subgroups is slightly different from that of a group, it relies on `Sets`:
```
structure Subgroup (G : Type* u_3*) [Group G] extends Submonoid G : Type*

A subgroup of a group G is a subset containing 1, closed under multiplication and closed under multiplicative inverse.

    carrier : Set G
    mul_mem' {a b : G} : a ∈ self.carrier → b ∈ self.carrier → a * b ∈ self.carrier
    one_mem' : 1 ∈ self.carrier
    inv_mem' {x : G} : x ∈ self.carrier → x⁻¹ ∈ self.carrier
```
We'll discuss what "sets" are next time, but for now just observe that given any type `G : Type*`, 
and any set `S : Set G`, we obtain for every `g : G` the type (of kind `Prop`) `g ∈ S`, that can be either true or false.

Observe in particular, as we've discussed for monoids, that "being a subgroup" is not a `Prop`-like
notion: the perspective is that, to each group `G`, we attach a new *type* `Subgroup G` whose terms
represent the different subgroups of `G`, seen as an underlying set and a collection of proofs that
the set is multiplicatively closed (a "mixin").

1. Another example of instance: every subgroup is a group
1. Coe, norm_num e norm_cast

#### [Quotients](https://github.com/faenuccio-teaching/M2Lyon2425/blob/afcb059590adbe169d3e03ce50277ef920a9b567/M2Lyon2425/Groups2_solutions.lean#L465)


#### Morphisms
## Rings

** Borrow from** https://github.com/faenuccio-teaching/GradCourse25/blob/master/GradCourse25/3_AlgebraicStructures_lecture.pdf **adding ring and grind**

1. Def, Ideals, `CommRing`, `IsDomain`  
2. `grind`, `ring`
3. `#synth CommRing ℤ`
4. [Units](https://github.com/faenuccio-teaching/M2Lyon2425/blob/afcb059590adbe169d3e03ce50277ef920a9b567/M2Lyon2425/Rings1_solutions.lean#L127)
5. [Ring Homs](https://github.com/faenuccio-teaching/M2Lyon2425/blob/afcb059590adbe169d3e03ce50277ef920a9b567/M2Lyon2425/Rings1_solutions.lean#L173)