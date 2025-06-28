import Mathlib

/- # A Glimpse of Category Theory in Lean

This file is a guided tour through category theory as formalized in Lean's mathlib.
It is designed for mathematicians who want to explore how category theory concepts
are expressed and manipulated in a proof assistant. We assume familiarity with
category theory concepts, and focus on how to work with them in Lean.

The goal is to learn enough tactics and library navigation to work with:
- Categories, functors, and natural transformations
- Adjunctions and the Yoneda lemma
- Limits and colimits
- Applications to algebraic geometry

Every exercise asks you to replace `sorry` with appropriate tactics or terms.
-/

open CategoryTheory

/- ## Categories and Morphisms

In mathlib, a category is a type class. Given a type `C`, we can make it into
a category by providing an instance of `Category C`. This gives us objects
(elements of type `C`) and morphisms between them.

For objects `X Y : C`, the type of morphisms from `X` to `Y` is written `X ⟶ Y`.
Identity morphisms are written `𝟙 X` and composition is `≫`.

Let's start with some basic exercises about morphisms.
-/

variable {C : Type*} [Category C]

example (X Y Z W : C) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    f ≫ (g ≫ h) = (f ≫ g) ≫ h := by
  -- This is associativity of composition
  rw [Category.assoc]

example (X Y : C) (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by
  -- This is the right identity law
  rw [Category.comp_id]

example (X Y : C) (f : X ⟶ Y) : 𝟙 X ≫ f = f := by
  -- Try using rw with the appropriate lemma name
  sorry

/- The `simp` tactic knows about the basic category theory identities.
When working with morphisms, `simp` will often solve goals involving
associativity and identity laws.

You can also use `rw` with specific lemma names instead of `simp` when you
want to be more explicit about which categorical law you're applying.
-/

/- ## Isomorphisms

An isomorphism in a category is a morphism with a two-sided inverse.
In mathlib, `IsIso f` is the typeclass asserting that `f` is an isomorphism.
The inverse of `f` is denoted `inv f`.
-/

example (X Y : C) (f : X ⟶ Y) [IsIso f] : f ≫ inv f = 𝟙 X := by
  -- This shows that f followed by its inverse gives the identity
  rw [IsIso.hom_inv_id]

example (X Y : C) (f : X ⟶ Y) [IsIso f] : inv f ≫ f = 𝟙 Y := by
  -- Try using rw with the appropriate lemma for the other direction
  sorry

/- Objects `X` and `Y` are isomorphic if there exists an isomorphism between them.
This is written `X ≅ Y`.

As with basic morphisms, you can use either `simp` (which knows about isomorphism
identities) or `rw` with specific lemma names when working with isomorphisms.
-/

example (X Y Z : C) (f : X ≅ Y) (g : Y ≅ Z) : X ≅ Z := by
  -- We can compose isomorphisms
  exact f ≪≫ g

/- ## Functors

A functor `F : C ⥤ D` sends objects and morphisms from category `C` to category `D`,
preserving identities and composition.

For an object `X : C`, its image under `F` is `F.obj X`.
For a morphism `f : X ⟶ Y`, its image is `F.map f : F.obj X ⟶ F.obj Y`.
-/

variable {D : Type*} [Category D]

example (F : C ⥤ D) (X : C) : F.map (𝟙 X) = 𝟙 (F.obj X) := by
  -- Functors preserve identities
  rw [F.map_id]

example (F : C ⥤ D) (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g := by
  -- Try using rw with the appropriate lemma for composition preservation
  sorry

/- We can compose functors using `⋙` -/

variable {E : Type*} [Category E]

example (F : C ⥤ D) (G : D ⥤ E) (X : C) :
    (F ⋙ G).obj X = G.obj (F.obj X) := by
  -- This is true by definition (definitional equality)
  rfl

example (F : C ⥤ D) (G : D ⥤ E) (X : C) :
    (F ⋙ G).obj X = G.obj (F.obj X) := by
  -- We can also be explicit about the lemma
  rw [Functor.comp_obj]

example (F : C ⥤ D) (G : D ⥤ E) (X Y : C) (f : X ⟶ Y) :
    (F ⋙ G).map f = G.map (F.map f) := by
  -- Try both approaches: is this true by definition, or do you need an explicit lemma?
  sorry

/- Again, you can use either `simp` (which knows about functor laws) or `rw`
with specific lemma names when working with functors.
-/

/- ## Natural Transformations

A natural transformation `α : F ⟶ G` between functors `F G : C ⥤ D`
assigns to each object `X : C` a morphism `α.app X : F.obj X ⟶ G.obj X`
such that the naturality square commutes.
-/

example (F G : C ⥤ D) (α : F ⟶ G) (X Y : C) (f : X ⟶ Y) :
    F.map f ≫ α.app Y = α.app X ≫ G.map f := by
  -- This is the naturality condition - Lean knows this as α.naturality f
  exact α.naturality f

/- Let's prove that natural transformations can be composed vertically -/

example (F G H : C ⥤ D) (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).app X = α.app X ≫ β.app X := by
  -- Try rw? to find the right lemma name, or use rfl if it's definitional
  sorry

/- The identity natural transformation is defined component-wise -/

example (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := by
  -- Again, try rw? to discover the lemma, or rfl if definitional
  sorry

/- As with functors, you can often use `simp` for natural transformation identities,
or use `rw?` to discover the specific lemma names when you want to understand
the underlying structure better.
-/

/- ## Adjunctions

An adjunction between functors `F : C ⥤ D` and `G : D ⥤ C` establishes
a bijection between morphisms `F.obj X ⟶ Y` and `X ⟶ G.obj Y`.

In mathlib, this is expressed as `F ⊣ G` (read "F is left adjoint to G").
-/

example (F : C ⥤ D) (G : D ⥤ C) [F ⊣ G] (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    ∃ g : X ⟶ G.obj Y, (Adjunction.ofLeftAdjoint F).homEquiv X Y f = g := by
  use (Adjunction.ofLeftAdjoint F).homEquiv X Y f
  rfl

/- Adjunctions give us unit and counit natural transformations -/

example (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) (X : C) :
    ∃ η : 𝟭 C ⟶ F ⋙ G, η.app X = adj.unit.app X := by
  sorry

/- ## The Yoneda Lemma

The Yoneda lemma states that for any functor `F : C ⥤ Type*` and object `X : C`,
natural transformations from the representable functor `yoneda.obj X` to `F`
are in bijection with elements of `F.obj X`.
-/

variable (F : C ⥤ Type*)

example (X : C) :
    (yoneda.obj X ⟶ F) ≃ F.obj X := by
  -- This is the Yoneda lemma
  exact yonedaLemma F X

/- Let's work with this bijection -/

example (X Y : C) (f : X ⟶ Y) :
    yoneda.map f = (yoneda.obj Y).map f := by
  sorry

/- ## Limits and Colimits

Limits and colimits are fundamental constructions in category theory.
A limit of a diagram is a universal cone over that diagram.

Let's work with terminal objects (limits of the empty diagram) -/

variable [HasTerminal C]

example : ∃ T : C, ∀ X : C, ∃! f : X ⟶ T, True := by
  use ⊤_ C
  intro X
  exact ⟨terminal.from X, fun _ _ => terminal.hom_ext _ _⟩

/- For any object, there's a unique morphism to the terminal object -/

example (X : C) : ∃! f : X ⟶ ⊤_ C, True := by
  sorry

/- Let's work with binary products (limits of spans) -/

variable [HasBinaryProducts C]

example (X Y : C) : ∃ P : C, ∃ (π₁ : P ⟶ X) (π₂ : P ⟶ Y),
    ∀ Z : C, ∀ (f : Z ⟶ X) (g : Z ⟶ Y), ∃! h : Z ⟶ P,
      h ≫ π₁ = f ∧ h ≫ π₂ = g := by
  use X ⨯ Y, Limits.prod.fst, Limits.prod.snd
  intro Z f g
  use Limits.prod.lift f g
  constructor
  · constructor
    · simp
    · simp
  · intro h ⟨hf, hg⟩
    rw [← hf, ← hg]
    simp

/- ## Functor Categories and Preservation of Limits

Functors can preserve or reflect limits. A functor `F : C ⥤ D` preserves
limits if it sends limit cones to limit cones.
-/

variable [HasTerminal C] [HasTerminal D]

-- A functor that preserves terminal objects
example (F : C ⥤ D) [PreservesLimit (Functor.empty C) F] :
    IsTerminal (F.obj (⊤_ C)) := by
  sorry

/- ## Applications to Algebraic Geometry

In algebraic geometry, many properties of morphisms can be expressed
as properties in the category of schemes. Let's explore etale morphisms.

Etale morphisms are morphisms of schemes that are locally of finite type,
flat, and unramified.
-/

-- Note: This section requires more advanced imports and may not work
-- without additional setup. It's included to show the connection.

variable {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)

/- A morphism is etale if it's locally of finite type, flat, and unramified -/

example [AlgebraicGeometry.LocallyOfFiniteType f]
        [AlgebraicGeometry.Flat f]
        [AlgebraicGeometry.Unramified f] :
    AlgebraicGeometry.Etale f := by
      sorry

/- This demonstrates how category theory provides a framework for
organizing geometric concepts in algebraic geometry. -/

/- ## Final Exercises

Here are some more challenging exercises that combine the concepts we've learned.
-/

-- Prove that isomorphic objects have isomorphic hom-sets
example (X X' Y : C) (e : X ≅ X') :
    (X ⟶ Y) ≃ (X' ⟶ Y) := by
  sorry

-- Show that adjoint functors preserve certain limits
example (F : C ⥤ D) (G : D ⥤ C) [F ⊣ G] [HasTerminal C] [HasTerminal D]
        [PreservesLimit (Functor.empty D) G] :
    IsTerminal (F.obj (⊤_ C)) := by
  sorry

-- The Yoneda embedding is full and faithful
example : FullyFaithful (yoneda : C ⥤ Cᵒᵖ ⥤ Type*) := by
  sorry

/- This concludes our tour of category theory in Lean. The key takeaways are:

1. Categories are type classes in Lean, making them easy to work with
2. The `simp` tactic knows about basic categorical identities
3. Functors, natural transformations, and adjunctions have natural formalizations
4. The Yoneda lemma provides powerful tools for working with representable functors
5. Limits and colimits can be characterized by their universal properties
6. Category theory provides a unifying framework for diverse mathematical areas

To continue learning, explore mathlib's extensive category theory library
and try applying these concepts to specific mathematical contexts.
-/
