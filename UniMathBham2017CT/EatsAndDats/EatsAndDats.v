
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.covyoneda.
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
  Proof.
    use dirprodpair.
    - simpl vertex.
      assert (three_is_finite : FiniteSets.isfinite three);
        apply isfinitestn.

    -
      use (three_rec_dep (λ x,
                          (forall y,
                              FiniteSets.isfinite
                                (@edge pullback_graph x y)))).
      + use (three_rec_dep
               (λ y, FiniteSets.isfinite
                       (@edge pullback_graph (stnpr 0) y))).
        apply isfiniteempty.
        apply isfiniteunit.
        apply isfiniteempty.
      + use (three_rec_dep
               (λ y, FiniteSets.isfinite
                       (@edge pullback_graph (stnpr 1) y)));
          apply isfiniteempty.
      + use (three_rec_dep
               (λ y, FiniteSets.isfinite
                       (@edge pullback_graph (stnpr 2) y))).
        apply isfiniteempty.
        apply isfiniteunit.
        apply isfiniteempty.
  Defined.

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


Section Filtered_Categories.

  Definition Diags_Have_Cocones (C : precategory) : UU
    := ∏ (g : finite_graph) (d : diagram g C), ishinh(∑(c:C), cocone d c).

  Definition filtered_category : UU := ∑ C : precategory, Diags_Have_Cocones C.

(* TODO: Do we need chosen cocones or is mere existence sufficient? Supposedly the latter is enough. This should be formalized
at some point, i.e. prove that already with the truncated notion,
for finite sets X we actually have colim (X, Yi) = Hom(X, colim Yi) *)

  Definition FilteredColims (C : precategory) : UU
    := ∑ (J : filtered_category) (F: functor (pr1 J) C), ColimCocone (diagram_from_functor (pr1 J) C F).

  Definition hasFilteredColims (C : precategory) : UU
    := ∏ (J : filtered_category) (F: functor (pr1 J) C), ishinh(ColimCocone (diagram_from_functor (pr1 J) C F)).

  Definition preserves_filtered_colimits {C D : precategory}(F : functor C D) : UU
   :=  ∏ (X : FilteredColims C),

    let J := (pr1 (pr1 X)) in
    let G := (pr1 (pr2 X)) in
    let g := (graph_from_precategory J) in
    let d := (diagram_from_functor J C G) in
    let CC := (pr2 (pr2 X)) in
    let cc := (pr2 (pr1 CC)) in
    let L := colim CC in
      isColimCocone d L cc -> isColimCocone (mapdiagram F d) (F L) (mapcocone F d cc).

  Definition FilteredColimsCategory : UU := ∑ (C : category), hasFilteredColims C.

  Definition isFinitelyPresentableObject {C : category} (x : ob C): UU := preserves_filtered_colimits(covyoneda C (homset_property C) x).

  Definition finitely_presentable_object (C : category) : UU := ∑ (x : ob C), isFinitelyPresentableObject x.

End Filtered_Categories.

Section Comprehension_Categories.

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

End FLCat_to
      exit
      CompCat.

Section CompCat_to_FLCat.
  Definition CompCat_to_FLCat : CompCat -> Finite_Limit_Category.
  Admitted.
End CompCat_to_FLCat.
