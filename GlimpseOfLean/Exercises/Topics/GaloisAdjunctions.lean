import GlimpseOfLean.Lib.TutoLib

open PiNotation

/- # Abstract non-sense 101: Galois adjunctions

In this file we will play with the simplest examples of adjunctions: Galois connections
between complete lattices. There is a lot about this topic in mathlib, but here we will
roll our own version for practice. This file builds the fundamental theory of these objects
and each lemma you prove there is named and can be reused to prove the next lemmas.
-/

namespace Tuto

section InfSup
variable  [PartialOrder X]

/-
In this section, `X` is a type equiped with a partial order relation. So you have access
to lemmas:
* `le_rfl {a : X} : a ≤ a`
* `le_trans {a b c : X} (h : a ≤ b) (h' : b ≤ c) : a ≤ c`
* `le_antisymm {a b : X} (h : a ≤ b) (h' : b ≤ a) : a = b`

Curly braces around arguments mean these arguments are implicits, Lean will infer
those arguments from context.

If you need to see a definition, say for `lowerBounds` below, you can open the contextual
menu by right-clicking on a word and then select "Go to definition", or you can simply
Ctrl-click on the word.
-/

/-- An element `x₀` is an infimum of a set `s` in `X` if every element
of `X` is a lower bound of `s` if and only if it below `x₀`.  -/
def isInf (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ lowerBounds s ↔ x ≤ x₀

lemma isInf.lowerBound {s : Set X} {x₀ : X} (h : isInf s x₀) : x₀ ∈ lowerBounds s := by
  sorry

/-- A set has at most one infimum. -/
def isInf.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isInf s x₀) (hx₁ : isInf s x₁) : x₀ = x₁ := by
  sorry

/-- An element `x₀` is an supremum of a set `s` in `X` if every element
of `X` is a lower bound of `s` if and only if it below `x₀`.  -/
def isSup (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ upperBounds s ↔ x₀ ≤ x

/-
The next lemma is proven by applying `isInf.lowerBound` to `X` equipped with
the opposite order relation. You don't need to understand precisely how this is
achieved since all proofs using this trick will be offered.
-/

lemma isSup.upperBound {s : Set X} {x₀ : X} (h : isSup s x₀) : x₀ ∈ upperBounds s :=
  isInf.lowerBound (X := OrderDual X) h

/-- A set has at most one supremum. -/
def isSup.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isSup s x₀) (hx₁ : isSup s x₁) : x₀ = x₁ :=
  isInf.eq (X := OrderDual X) hx₀ hx₁

/-- A function from `Set X` to `X` is an infimum function if it sends every set
to an infimum of this set. -/
def isInfFun (I : Set X → X) :=
  ∀ s : Set X, isInf s (I s)

/-- A function from `Set X` to `X` is an supremum function if it sends every set
to an supremum of this set. -/
def isSupFun (S : Set X → X) :=
  ∀ s : Set X, isSup s (S s)

/- The next lemma is the first crucial result if this file. If `X` admits an
infimum function then it automatically admits a supremum function. -/

lemma isSup_of_isInf {I : Set X → X} (h : isInfFun I) : isSupFun (fun s ↦ I (upperBounds s)) := by
  sorry

/- Of course we also have the dual result constructing an infimum function from
a supremum one. -/

lemma isInf_of_isSup {S : Set X → X} (h : isSupFun S) : isInfFun (fun s ↦ S (lowerBounds s)) :=
  isSup_of_isInf (X := OrderDual X) h

/- We are now ready for the first main definition of this file: complete lattices. -/

/-- A complete lattice is a type equipped with a partial order, an infimum function and
a supremum function. For instance `X = Set Y` equipped with the inclusion order,
the intersection function and the union function is a complete lattice. -/
class CompleteLattice (X : Type) [PartialOrder X] where
  I : Set X → X
  I_isInf : isInfFun I
  S : Set X → X
  S_isSup : isSupFun S

/-- Turning a complete lattice `X` into the dual one. Lean will automatically pickup this
construction when using the `OrderDual` trick as above. -/
instance (X : Type) [PartialOrder X] [CompleteLattice X] : CompleteLattice (OrderDual X) where
  I := CompleteLattice.S (X := X)
  I_isInf := CompleteLattice.S_isSup (X := X)
  S := CompleteLattice.I (X := X)
  S_isSup := CompleteLattice.I_isInf (X := X)

/- We can now use the first main result above  to build a complete lattice from
either an infimum or a supremum function on a partialy ordered type. -/

/-- Building a complete lattice structure from an infimum function on a partialy ordered type. -/
def CompleteLattice.mk_of_Inf {I : Set X → X} (h : isInfFun I) : CompleteLattice X where
 I := I
 I_isInf := h
 S := fun s ↦ I (upperBounds s)
 S_isSup := isSup_of_isInf h

/-- Building a complete lattice structure from an supremum function on a partialy ordered type. -/
def CompleteLattice.mk_of_Sup {S : Set X → X} (h : isSupFun S) : CompleteLattice X where
 I := fun s ↦ S (lowerBounds s)
 I_isInf := isInf_of_isSup h
 S := S
 S_isSup := h

/- Until the end of this section, `X` will be a complete lattice. -/
variable [CompleteLattice X]

/-- The infimum function on a complete lattice. -/
notation "Inf" => CompleteLattice.I

/-- The supremum function on a complete lattice. -/
notation "Sup" => CompleteLattice.S

/- We now restate a couple of lemmas proven above in terms of complete lattices. -/

lemma lowerBound_Inf (s : Set X) : Inf s ∈ lowerBounds s :=
  (CompleteLattice.I_isInf _).lowerBound

lemma upperBound_Sup (s : Set X) : Sup s ∈ upperBounds s :=
  (CompleteLattice.S_isSup _).upperBound

/- We now prove a series of lemmas asserting that `Inf` (and then `Sup` by duality)
behave according to your intuition. You should feel free to skip those and jump to
the adjunction section if you think you would be able to prove them and you want to
see more interesting things.

In the first lemma below, you will probably want to use
`lowerBounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : lowerBounds t ⊆ lowerBounds s`
or reprove it as part of your proof.
-/

lemma Inf_subset {s t : Set X} (h : s ⊆ t): Inf t ≤ Inf s := by
  sorry

lemma Sup_subset {s t : Set X} (h : s ⊆ t): Sup s ≤ Sup t :=
  Inf_subset (X := OrderDual X) h

lemma Inf_pair {x x' : X} : x ≤ x' ↔ Inf {x, x'} = x := by
  sorry

lemma Sup_pair {x x' : X} : x ≤ x' ↔ Sup {x, x'} = x' := by
  rw [Set.pair_comm x x']
  exact Inf_pair (X := OrderDual X)

lemma Inf_self_le (x : X) : Inf {x' | x ≤ x'} = x := by
  sorry

lemma Sup_le_self (x : X) : Sup {x' | x' ≤ x} = x :=
  Inf_self_le (X := OrderDual X) x

end InfSup

section Adjunction
/- We are now ready for the second central definition of this file: adjunctions between
ordered types. -/

/-- A pair of functions `l` and `r` between ordered types are adjoint if
`∀ x y, l x ≤ y ↔ x ≤ r y`. One also say they form a Galois connection.
Here `l` stands for "left" and `r` stands for "right". -/
def adjunction [PartialOrder X] [PartialOrder Y] (l : X → Y) (r : Y → X) :=
  ∀ x y, l x ≤ y ↔ x ≤ r y

/- The example you need to keep in mind is the adjunction between direct image
and inverse image. Given `f : α → β`, we have:
* `Set.image f : Set α → Set β` with notation `f ''`
* `Set.preimage f : Set β → Set α` with notation `f ⁻¹'`
 -/

example {α β : Type} (f : α → β) : adjunction (Set.image f) (Set.preimage f) := by
  intros s t
  exact Set.image_subset_iff

/- In this remaining of the section, `X` and `Y` are complete lattices. -/
variable [PartialOrder X] [CompleteLattice X] [PartialOrder Y] [CompleteLattice Y]

/- We now come to the second main theorem of this file: the adjoint functor theorem for
complete lattices. This theorem says that a function between complete lattices is
a left adjoint (resp. right adjoint) if and only if it commutes with `Sup` (resp. with `Inf`).

We first define the candidate right adjoint (without making any assumption on the original
map).
  -/

/-- Constructs a candidate right adjoint for a map between complete lattices.
This is an actual adjoint if the map commutes with `Sup`, see `adjunction_of_Sup`. -/
def mk_right (l : X → Y) : Y → X := fun y ↦ Sup {x | l x ≤ y}

/- The proof of the theorem below isn't long but it isn't completely obvious either.
First you need to understand the notations in the statement. `l '' s` is the direct image
of `s` under `l`. This `''` is notation for `Set.image`. Putting your cursor on this
notation and using the contextual menu to "jump to definiion" will bring you to the file
defining `Set.image` and containing lots of lemmas about it. The ones that are used in
the reference solutions are

* `Set.image_pair : (f : α → β) (a b : α) : f '' {a, b} = {f a, f b}`
* `Set.image_preimage_subset (f : α → β) (s : Set β) : f '' (f ⁻¹' s) ⊆ s`

Proof hint: one direction is easy and doesn't use the crucial assumption. For
the other direction, you should probably first prove that `Monotone l`, ie
`∀ ⦃a b⦄, a ≤ b → l a ≤ l b`.
-/

theorem adjunction_of_Sup {l : X → Y} (h : ∀ s : Set X, l (Sup s) = Sup (l '' s)) :
    adjunction l (mk_right l) := by
  sorry

/- Of course we can play the same game to construct left adjoints. -/

/-- Constructs a candidate left adjoint for a map between complete lattices.
This is an actual adjoint if the map commutes with `Inf`, see `adjunction_of_Inf`. -/
def mk_left (r : Y → X) : X → Y := fun x ↦ Inf {y | x ≤ r y}

theorem adjunction_of_Inf {r : Y → X} (h : ∀ s : Set Y, r (Inf s) = Inf (r '' s)) :
    adjunction (mk_left r) r :=
  fun x y ↦ (adjunction_of_Sup (X := OrderDual Y) (Y := OrderDual X) h y x).symm

end Adjunction

section Topology
/- In this section we apply the theory developped above to point-set topology.
Our first goal is to endow the type `Topology X` of topologies on a given type
with a complete lattice structure. We then turn any map `f : X → Y` into an
adjunction `(f⁎, f ^*)` between `Topology X` and `Topology Y` and use it
to build the product topology. Of course mathlib knows all this, but we'll
continue to build our own theory.
-/


@[ext]
structure Topology (X : Type) where
  isOpen : Set X → Prop
  isOpen_unionᵢ : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → isOpen (⋃ i, s i)
  isOpen_interᵢ : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → Finite ι → isOpen (⋂ i, s i)

/- Let's run two quick sanity checks on our definition since so many textbooks include redundant
conditions it the definition of topological spaces. -/

lemma isOpen_empty (T : Topology X) : T.isOpen ∅ := by
  have : (∅ : Set X) = ⋃ i : Empty, i.rec
  · rw [Set.unionᵢ_of_empty]
  rw [this]
  exact T.isOpen_unionᵢ Empty.rec

lemma isOpen_univ (T : Topology X) : T.isOpen Set.univ := by
  have : (Set.univ : Set X) = ⋂ i : Empty, i.rec
  · rw [Set.interᵢ_of_empty]
  rw [this]
  exact T.isOpen_interᵢ  Empty.rec (Finite.of_fintype Empty)

/- The `ext` attribute on the definition of `Topology` tells Lean to automatically build the following
extensionality lemma:
`Topology.ext_iff (T T' : Topology X), T = T' ↔ x.isOpen = y.isOpen`
and it also registers this lemma for use by the `ext` tactic (we will come back to this below).
-/

/-- We order `Topology X` using the order dual to the order induced by
`Set (Set X)`. There are good reasons for this choice but they are beyond the scope of this
tutorial. -/
instance : PartialOrder (Topology X) :=
PartialOrder.lift (β := OrderDual $ Set (Set X)) Topology.isOpen (fun T T' ↦ (Topology.ext_iff T T').2)

/-- The supremum function on `Topology X`. -/
def SupTop (s : Set (Topology X)) : Topology X where
  isOpen := fun V ↦ ∀ T ∈ s, T.isOpen V
  isOpen_unionᵢ := by
    intros ι t ht a ha
    exact a.isOpen_unionᵢ fun i ↦ ht i a ha
  isOpen_interᵢ := by
    intros ι t ht hι a ha
    exact a.isOpen_interᵢ (fun i ↦ ht i a ha) hι

/-
Because the supremum function above comes from the supremum function of `OrderDual (Set (Set X))`,
it is indeed a supremum function. We could state an abstract lemma saying that, but here a direct
proof is just as easy and a lot of fun.
-/
lemma isSup_SupTop : isSupFun (SupTop : Set (Topology X) → Topology X) :=
fun _ _ ↦ ⟨fun hT _ hV _ hs ↦ hT hs hV, fun hT T' hT' _ hV ↦ hT hV T' hT'⟩

/- We can use our abtract theory to get an infimum function for free, hence a complete lattice
structure on `Topology X`.
Note that our abstract theory is indeed doing non-trivial work: the infimum function does *not*
come from `OrderDual (Set (Set X))`.
-/

instance : CompleteLattice (Topology X) := CompleteLattice.mk_of_Sup isSup_SupTop

/- Let us restate in complete lattice notation what our construction of `Sup` was. The proof
is simply saying "this is true by definition". -/

lemma isOpen_Sup {s : Set (Topology X)} {V : Set X} : (Sup s).isOpen V ↔ ∀ T ∈ s, T.isOpen V :=
  Iff.rfl

/- We now start bulding our adjunction between `Topology X` and `Topology Y` induced by any
map `f : X → Y`. We will build the left adjoint by hand and then invoke our adjoint functor
theorem.
-/

def push (f : X → Y) (T : Topology X) : Topology Y where
  isOpen := fun V ↦ T.isOpen (f ⁻¹' V)
  isOpen_unionᵢ := by
    sorry
  isOpen_interᵢ := by
    sorry

postfix:1024 "⁎" => push

/-- A map `f : X → Y` is continuous with respect to topologies `T` and `T'` if the preimage of
every open set is open.-/
def Continuous (T : Topology X) (T' : Topology Y) (f : X → Y) :=  f ⁎ T ≤ T'

/- Let us check the definition is indeed saying what we claimed it says. -/
example (T : Topology X) (T' : Topology Y) (f : X → Y) :
  Continuous T T' f ↔ ∀ V, T'.isOpen V → T.isOpen (f ⁻¹' V) :=
Iff.rfl

/- Note how the following proof uses the `ext` tactic which knows that two topologies are
equal iff they have the same open sets thanks to the `ext` attribute on the definition
of `Topology`. -/

lemma push_push (f : X → Y) (g : Y →Z) (T : Topology X) :
    g ⁎ (f ⁎ T) = (g ∘ f) ⁎ T := by
  ext V
  exact Iff.rfl

/- We want a right adjoint for `f ⁎` so we need to check it commutes with `Sup`.
You may want to use
`Set.ball_image_iff : (∀ y ∈ f '' s, p y) ↔ ∀ x ∈ s, p (f x)`
where "ball" stands for "bounded for all", ie `∀ x ∈ ...`.
-/

lemma push_Sup (f : X → Y) {t : Set (Topology X)} : f ⁎ (Sup t) = Sup (f ⁎ '' t) := by
  sorry

def pull (f : X → Y) (T : Topology Y) : Topology X := mk_right (push f) T

postfix:1024 "^*" => pull

def ProductTopology {ι : Type} {X : ι → Type} (T : Π i, Topology (X i)) : Topology (Π i, X i) :=
Inf (Set.range (fun i ↦ (fun x ↦ x i) ^* (T i)))

lemma ContinuousProductTopIff {ι : Type} {X : ι → Type} (T : Π i, Topology (X i))
  {Z : Type} (TZ : Topology Z) {f : Z → Π i, X i}:
    Continuous TZ (ProductTopology T) f ↔ ∀ i,  Continuous TZ (T i) (fun z ↦ f z i) := by
sorry

end Topology


namespace SubGroups

@[ext]
structure Subgroup (G : Type) [Group G] where
  carrier : Set G
  one_mem : 1 ∈ carrier
  mul_mem : ∀ ⦃x y : G⦄, x ∈ carrier → y ∈ carrier → x*y ∈ carrier
  inv_mem : ∀ ⦃x : G⦄, x ∈ carrier → x⁻¹ ∈ carrier

variable {G : Type} [Group G]

instance : PartialOrder (Subgroup G) := PartialOrder.lift Subgroup.carrier (fun H H' ↦ (Subgroup.ext_iff H H').2)

def SubgroupInf (s : Set (Subgroup G)) : Subgroup G where
  carrier := ⋂ H ∈ s, H.carrier
  one_mem := sorry
  mul_mem := sorry
  inv_mem := sorry

lemma SubgroupInf_is_Inf : isInfFun (SubgroupInf : Set (Subgroup G) → Subgroup G) := by
  sorry

instance : CompleteLattice (Subgroup G) := CompleteLattice.mk_of_Inf SubgroupInf_is_Inf

def forget (H : Subgroup G) : Set G := H.carrier

def generate : Set G → Subgroup G := mk_left forget

lemma generate_forget_adjunction : adjunction (generate : Set G → Subgroup G) forget := by
  sorry

variable {G' : Type} [Group G']

def pull (f : G →* G') (H' : Subgroup G') : Subgroup G where
  carrier := f ⁻¹' H'.carrier
  one_mem := sorry
  mul_mem := sorry
  inv_mem := sorry

/- Let's be really lazy and define subgroup push-forward by adjunction. -/

def push (f : G →* G') : Subgroup G → Subgroup G' := mk_left (pull f)

lemma push_pull_adjunction (f : G →* G') : adjunction (push f) (pull f) := by
  sorry

end SubGroups

section
/- Our next concrete target is
`push_generate (f : G →* G') (S : Set G) : push f (generate S) = generate (f '' S)`

which will require a couple more abstract lemmas. -/

variable {X : Type} [PartialOrder X] [CompleteLattice X]
         {Y : Type} [PartialOrder Y] [CompleteLattice Y]


lemma unique_left {l l' : X → Y} {r : Y → X} (h : adjunction l r) (h' : adjunction l' r) :
    l = l' := by
  sorry

lemma unique_right {l : X → Y} {r r' : Y → X} (h : adjunction l r) (h' : adjunction l r') :
    r = r' := by
 sorry

variable {Z : Type} [PartialOrder Z] [CompleteLattice Z]

lemma adjunction_compose {l : X → Y} {r : Y → X} (h : adjunction l r)
  {l' : Y → Z} {r' : Z → Y} (h' : adjunction l' r') : adjunction (l' ∘ l) (r ∘ r') := by
  sorry

end

namespace SubGroups
variable {G : Type} [Group G] {G' : Type} [Group G']

/- As a last challenge, we propose the following lemma. -/

lemma push_generate (f : G →* G') (S : Set G) : push f (generate S) = generate (f '' S) := by
  sorry

end SubGroups
end Tuto
