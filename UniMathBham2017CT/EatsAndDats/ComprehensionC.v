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

Definition ctx_extension {C : category} (D : comprehension_cat_structure C) : disp_functor _ _ _  := pr1 (pr2 (pr2 D)).

Definition canonical_pr {C : category} {D : comprehension_cat_structure C} (Γ : C) (A : (Ty D) Γ) : (disp_codomain C) Γ :=
  (ctx_extension D) _ A.

Definition comp_ext {C : category} {D : comprehension_cat_structure C} (Γ : C) (A : Ty D Γ) : C := (pr1 (canonical_pr Γ A)).

Local Notation "Γ ◂ A" := (comp_ext Γ A) (at level 30).