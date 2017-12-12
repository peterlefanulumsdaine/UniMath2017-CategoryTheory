Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.equivalences.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences_bis.


Definition preserves_cartesianness
           {C C' : category}
           {F : functor C C'}
           {D} {D'}
           (FF : disp_functor F D D') : UU
  :=
    ∏ (c c' : C) (f : C⟦c, c'⟧)
      (d : D c) (d' : D c')
      (ff : d -->[f] d'),
    is_cartesian ff -> is_cartesian (#FF ff).




Section fix_disp_adjunction.

Context {C C' : category}
        (A : adjunction C C')
        {D : disp_cat C}
        {D': disp_cat C'}
        (X : disp_adjunction A D D').
Let F : functor _ _ := left_adjoint A.
Let G : functor _ _ := right_adjoint A.

Let FF : disp_functor _ D D' := left_adj_over X.
Let GG : disp_functor _ D' D := right_adj_over X.

Section DispHomSetIso_from_Adjunction.

  Let η := unit_from_are_adjoints A.
  Let ε := counit_from_are_adjoints A.

  Definition homset_conj_inv {c : C} {c' : C'} (g : C⟦c, G c'⟧)
             (d : D c) (d' : D' c') :
      (d -->[g] GG _ d') -> (FF _ d -->[#F g · adjcounit A _] d').
  Proof.
  intro alpha.
  set (FFalpha := disp_functor_on_morphisms FF alpha).
  exact (comp_disp FFalpha (counit_over X _ _)).
  Defined.

  Definition homset_conj {c : C} {c' : C'} (f : C'⟦F c, c'⟧)
             (d : D c) (d' : D' c') :
      (FF _ d -->[f] d') -> (d -->[adjunit A _ · #G f] GG _ d').
  Proof.
  intro beta.
  set (GGbeta := disp_functor_on_morphisms GG beta).
  exact (comp_disp (unit_over X _ _) GGbeta).
  Defined.

  Lemma homset_conj_inv_after_conj {c : C} {c' : C'} (f : C'⟦F c, c'⟧) (d : D c) (d' : D' c') (beta : FF _ d -->[f] d') : transportf _ (φ_adj_inv_after_φ_adj A f) (homset_conj_inv _ d d' (homset_conj f d d' beta)) = beta.
  unfold homset_conj.
  unfold homset_conj_inv.
(* TODO: finish this proof, assuming the lemma is true! *)
  unfold φ_adj_inv_after_φ_adj.

  (* simpl in gamma. *)
  (* assert (equiv : (adjunit A) c · # (right_functor A) (# F g · (adjcounit A) c') = g). *)
  (* apply (φ_adj_after_φ_adj_inv A g). *)
  (* exact (transportf _ equiv gamma). *)
  (* Defined. *)

  (* Definition homset_conjinv {c : C} {c' : C'} (g : C⟦c, G c'⟧) *)
  (*            (d : D c) (d' : D' c') : *)
  (*     (FF _ d -->[#F g · adjcounit A _] d') -> (d -->[g] GG _ d'). *)
  (* Proof. *)
  (* intro beta. *)
  (* set (GGbeta := disp_functor_on_morphisms GG beta). *)
  (* set (gamma := comp_disp (unit_over X _ _) GGbeta). *)
  (* simpl in gamma. *)
  (* assert (equiv : (adjunit A) c · # (right_functor A) (# F g · (adjcounit A) c') = g). *)
  (* apply (φ_adj_after_φ_adj_inv A g). *)
  (* exact (transportf _ equiv gamma). *)
  (* Defined. *)

  
    
  Lemma dispadjunction_hom_weq (c : C) (c' : C') (g : C⟦c, G c'⟧) (d : D c) (d' : D' c') :
      (d -->[g] GG _ d') ≃ (FF _ d -->[#F g · adjcounit A _] d').
  Proof.


  Definition φ_adj {A : C} {B : D} : F A --> B → A --> G B
    := λ f : F A --> B, η _ · #G f.

  Definition φ_adj_inv {A : C} {B : D} : A --> G B → F A --> B
    := λ g : A --> G B, #F g · ε _ .
  
  
End DispHomSetIso_from_Adjunction.



Lemma right_over_adj_preserves_cartesianness : preserves_cartesianness GG.
Proof.
  unfold preserves_cartesianness.
  intros c c' f d d' ff ff_cart.
  intros c'' g d'' h.
  unfold is_cartesian in ff_cart.

  (** Path to happiness:

- construct homset-isomorphisms defined by a displayed adjunction;
  in particular,
  d -->[g] GG e  ≃   FF d -->[F g · counit _ ] e
- this equivalence is the equivalence in the first component of
   an equivalence between sigma types as occurring in def of [is_cartesian]
- use lemma saying that given an equivalence of types where one type is contractible,
  the other is, too
*)

Abort.

End fix_disp_adjunction.
