
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.

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

Definition CompCat : Type.
Admitted.

Definition CompCat_to_FLCat : FLCat -> CompCat.
Admitted.

Definition FLCat_to_FLCat : CompCat -> FLCat.
Admitted.

