(* TODO Upstream all of this to TypeTheory or UniMath *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import TypeTheory.Displayed_Cats.DisplayedCatFromCwDM.
Require Import TypeTheory.OtherDefs.DM.
Require Import TypeTheory.Displayed_Cats.ComprehensionC.

Definition base_ob {C : category} {D : disp_cat C} {c : C} (d : D c) : C := c.

Definition Ty {C : category} (D : comprehension_cat_structure C) : disp_cat C := pr1 D.

Definition Ty_cleaving {C : category} (D : comprehension_cat_structure C) : cleaving (Ty D) := pr1 (pr2 D).

Definition ctx_extension {C : category} (D : comprehension_cat_structure C) : disp_functor _ _ (disp_codomain C)  := pr1 (pr2 (pr2 D)).

Definition ctx_extension_cartesian {C : category} (D : comprehension_cat_structure C)
  : is_cartesian_disp_functor (ctx_extension D).
Proof.
  apply pr2.
  Defined.



Definition canonical_pr {C : category} {D : comprehension_cat_structure C} (Γ : C) (A : (Ty D) Γ) : (disp_codomain C) Γ :=
  (ctx_extension D) _ A.

Definition substitution {C : category} {D : comprehension_cat_structure C}
           {Γ Δ : C}
           (σ : Γ --> Δ)
           (A : Ty D Δ) : Ty D Γ.
Proof.
  use object_of_cartesian_lift.
  exact Δ.
  exact A.
  exact σ.
  apply Ty_cleaving.
Defined.

Local Notation "A [ σ ]" := (substitution σ A) (at level 30).

(* TODO prove properties of substitution *)

Definition comp_ext {C : category} {D : comprehension_cat_structure C} (Γ : C) (A : Ty D Γ) : C := (pr1 (canonical_pr Γ A)).

Local Notation "Γ ◂ A" := (comp_ext Γ A) (at level 30).

Definition Tm {C : category} {D : comprehension_cat_structure C} (Γ : C) (A : Ty D Γ) : UU
  := ∑ (t : Γ --> (Γ ◂ A)) , (pr2 (canonical_pr Γ A)) ∘ t = (identity _).  

Definition cartesian_lift_to_map {C : category} {D : comprehension_cat_structure C}
           {Γ Δ : C}
           (σ : Γ --> Δ)
           (A : Ty D Δ) : (Γ ◂ substitution σ A) --> Δ ◂ A.
Proof.
  apply (disp_functor_on_morphisms (ctx_extension D) (Ty_cleaving D Δ Γ σ A)).
  Defined.

Definition comp_ext_wuniversal {C : category} {D : comprehension_cat_structure C}
           {Γ Δ : C}
           (σ : Γ --> Δ)
           (A : Ty D Δ)
           (t : Tm Γ (substitution σ A)) : Γ --> (Δ ◂ A).
Proof.
  use compose.
  exact (Γ ◂ (substitution σ A)).
  exact (pr1 t).
  apply cartesian_lift_to_map.
  Defined.



Definition pseudo_comp_functor {C C' : category}
           {D : comprehension_cat_structure C}
           {D' : comprehension_cat_structure C'}
           (F : functor  C C')
           (FF : disp_functor F (Ty D) (Ty D')) 
           (isc : is_cartesian_disp_functor FF) : UU
  := ∏ (Γ : C) (A : Ty D Γ) , iso (F (Γ ◂ A))( (F Γ) ◂ (FF _ A)). 

