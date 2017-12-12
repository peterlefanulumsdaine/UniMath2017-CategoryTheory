
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Section FiniteLimits.
  Definition isfinite (G : graph) : hProp
    := hconj (isfinite (vertex G))
             (∀ x y : vertex G, isfinite (edge x y)).

  (* TODO: add annotation upstream to put [graph] into [UU] (is currently in [Type]). *)
  Definition finite_graph : UU
    := ∑ G : graph, isfinite G.
 (* Note: if this errors, check you are invoking Coq with '-type-in-type'. *)
  Coercion graph_of_finite_graph := (fun G => pr1 G) : finite_graph -> graph.
  
  Definition Finite_Lims (C : precategory) : UU
    := ∏ (g : finite_graph) (d : diagram g C), LimCone d.

  Definition has_Finite_Lims (C : precategory) : UU
    := ∀ (g : finite_graph) (d : diagram g C), ishinh (LimCone d).

End FiniteLimits.

Definition FL_category : UU
  := ∑ C : category, Finite_Lims C.
(* Note: we assume finite-limit categories are given with _chosen_ finite limits.  For univalent categories, this should be equivalent to just assuming finite limits exist [has_Finite_Lims] by uniqueness of limits, but for general categories, the “chosen” version seems to be more natural.  *)

(* I can't find the definition of cartesian functor in the library... this is a place holder *)

Definition cartesian_functor {C : category} (E F : disp_cat C) : UU.
Admitted.

Definition CompCat : UU
   := ∑(C : category) (E : fibration C), cartesian_functor (pr1 E) (disp_codomain C).

Definition CompCat_to_FLCat : FL_category -> CompCat.
Admitted.

Definition FLCat_to_FLCat : CompCat -> FL_category.
Admitted.

