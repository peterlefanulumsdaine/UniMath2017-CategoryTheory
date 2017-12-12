
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import TypeTheory.Displayed_Cats.ComprehensionC.

Section Finite_Limits.

  (* Note: name chosen for consistency with [UniMath.Combinatorics.FiniteSets.isfinite] *)
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

  Lemma pullback_graph_finite : isfinite pullback_graph.
    Admitted.

  Lemma Limit_From_Finite_Lims {C : precategory} (H : Finite_Lims C) {g : graph} (hg : isfinite g) (d : diagram g C) : LimCone d.
  Proof.
    exact (H (g ,, hg) d).
    Defined.
  
  Lemma Pullbacks_from_Finite_Lims (C : precategory) : Finite_Lims C -> Pullbacks C.
  Proof.
    intro H.
    unfold Pullbacks.
    intros a b c f g.
    unfold Pullback.
    use Limit_From_Finite_Lims.
    assumption.
    use pullback_graph_finite.
    Defined.

End Finite_Limits.

Section Finite_Limit_Categories.

Definition Finite_Limit_Category : UU
  := ∑ C : category, Finite_Lims C.
(* Note: we assume finite-limit categories are given with _chosen_ finite limits.  For univalent categories, this should be equivalent to just assuming finite limits exist [has_Finite_Lims] by uniqueness of limits, but for general categories, the “chosen” version seems to be more natural.  *)

End Finite_Limit_Categories.

Section Comprehension_Categories.
<<<<<<< Updated upstream
  
=======

>>>>>>> Stashed changes
  Definition CompCat : UU
    := ∑(C : category), comprehension_cat_structure C.
  
End Comprehension_Categories.

Section FLCat_to_CompCat.
  
  Definition codomain_fibration : ∏ (C : category),
                                  Pullbacks C -> cleaving (disp_codomain C).
  Proof.
    intros C pb.
    intros c c' f d.
    assert (p : Pullback _ (pr2 d) f) by (apply pb).
    exists (lim p ,, PullbackPr2 _ p).
    exists ((PullbackPr1 _ p ,, PullbackSqrCommutes _ p)).
    apply isPullback_cartesian_in_cod_disp.
    apply equiv_isPullback_2.
    exact (pr2 C).
    apply (isPullback_Pullback C (pr2 C) p).
  Defined.

  Definition FLCat_to_CompCat : Finite_Limit_Category -> CompCat.
  Proof.
    intro F.
    set (C := pr1 F).
    exists C.
    exists (disp_codomain C).
    exists (codomain_fibration C (Pullbacks_from_Finite_Lims C (pr2 F))).
    use tpair.
    - apply disp_functor_identity.
    - intros c c' f d d' ff H.
      exact H.
  Defined.

End FLCat_to_CompCat.

Section CompCat_to_FLCat.
  Definition CompCat_to_FLCat : CompCat -> Finite_Limit_Category.
  Admitted.
End CompCat_to_FLCat.
