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

Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import TypeTheory.Displayed_Cats.ComprehensionC.

Section fix_disp_adjunction.

Context {C C' : category}
        (A : adjunction C C')
        {D : disp_cat C}
        {D': disp_cat C'}
        (X : disp_adjunction A D D').
Let F := left_functor A.
Let G := right_functor A.

Let FF : disp_functor F D D' := left_adj_over X.
Let GG : disp_functor G D' D := right_adj_over X.

Let η : functor_identity C ⟹ F ∙ G := adjunit A.
Let ε : G ∙ F ⟹ functor_identity C' := adjcounit A.
Let ηη : disp_nat_trans η (disp_functor_identity D) (disp_functor_composite FF GG)
    := unit_over X.
Let εε : disp_nat_trans ε (disp_functor_composite GG FF) (disp_functor_identity D')
    := counit_over X.

Local Open Scope hide_transport_scope.

Section DispHomSetIso_from_Adjunction.
  
  Definition homset_conj_inv {c : C} {c' : C'} (g : C⟦c, G c'⟧)
             (d : D c) (d' : D' c') :
      (d -->[g] GG _ d') -> (FF _ d -->[#F g ·  ε _] d').
  Proof.
    intro alpha.
    exact (comp_disp (# FF alpha) (εε _ _)).
  Defined.
  
  Definition homset_conj {c : C} {c' : C'} (g : C⟦c, G c'⟧)
  (d : D c) (d' : D' c') : 
     (FF _ d -->[#F g ·  ε _] d') -> (d -->[g] GG _ d'). 
  Proof. 
    intro beta.
    set (equiv := φ_adj_after_φ_adj_inv A g
                : η c · # G (# F g · ε c') = g).
    exact (transportf _ equiv (comp_disp (ηη _ _) (# GG beta))).
  Defined.
  
(* Alternative symmetric definition : *)
  Definition homset_conj' {c : C} {c' : C'} (f : C'⟦F c, c'⟧)
            (d : D c) (d' : D' c') :
     (FF _ d -->[f] d') -> (d -->[η _ · #G f] GG _ d').
  Proof.
    intro beta.
    exact (comp_disp (ηη _ _) (# GG beta)).
  Defined.

  Lemma homset_conj_inv_after_conj {c : C} {c' : C'} (g : C⟦c, G c'⟧)
        (d : D c) (d' : D' c')
        (beta : FF _ d -->[#F g · ε _] d') :
    homset_conj_inv _ _ _ (homset_conj g d d' beta) = beta.
  Proof.
    Open Scope mor_disp.
    unfold homset_conj.
    unfold homset_conj_inv.
    (*
    etrans.
    - eapply (maponpaths_2 comp_disp).
      apply disp_functor_transportf.
    - etrans.
      apply mor_disp_transportf_postwhisker.
      etrans. eapply (maponpaths_2 (transport). *)
    
    rewrite disp_functor_transportf.
    rewrite mor_disp_transportf_postwhisker.
    rewrite disp_functor_comp.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite assoc_disp_var.
    rewrite 2 transport_f_f.
    cbn.
    set (nat_εε := disp_nat_trans_ax εε beta).
    cbn in nat_εε. rewrite nat_εε. clear nat_εε.
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite assoc_disp.
    unfold transportb.
    rewrite 2 transport_f_f.
    (* Note : there should probably be an accessor function for this *)
    assert (triangle1 : # FF (ηη c d);; εε (F c) (FF c d) =
                        transportb _ (triangle_id_left_ad A c ) (id_disp _))
      by (exact ((pr1 (pr2 X)) c d)).
    cbn in triangle1.
    rewrite triangle1.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite id_left_disp.
    unfold transportb.
    rewrite 2 transport_f_f.
    intermediate_path (transportf _ (idpath _) beta).
    - apply maponpaths_2, homset_property.
    - apply idpath.
    Close Scope mor_disp.
  Defined.
  
(*
  Lemma homset_conj_inv_after_conj' {c : C} {c' : C'} (f : C'⟦F c, c'⟧)
        (d : D c) (d' : D' c')
        (beta : FF _ d -->[f] d') :
    transportf _ (φ_adj_inv_after_φ_adj A f) (homset_conj_inv _ _ _ (homset_conj' f d d' beta)) = beta. 
 *)
Print homset_conj_inv_after_conj.  
  Lemma homset_conj_after_conj_inv {c : C} {c' : C'} (g : C⟦c, G c'⟧)
        (d : D c) (d' : D' c')
        (alpha : d -->[g] GG _ d') :
    homset_conj _ _ _ (homset_conj_inv g d d' alpha) = alpha. 
  Proof.
    Open Scope mor_disp.
    unfold homset_conj.    
    unfold homset_conj_inv.
    rewrite disp_functor_comp.
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite assoc_disp.
    unfold transportb.
    rewrite 2 transport_f_f.
    cbn.
    set (nat_ηη := disp_nat_trans_ax_var ηη alpha).
    cbn in nat_ηη. rewrite nat_ηη. clear nat_ηη.
    rewrite mor_disp_transportf_postwhisker.
    rewrite assoc_disp_var.
    rewrite 2 transport_f_f.
    assert (triangle2 : (ηη (G c') (GG c' d');; # GG (εε c' d')) =
       transportb _ (triangle_id_right_ad A c') (id_disp _)) by (exact (pr2 (pr2 X) c' d')).
    cbn in triangle2.
    rewrite triangle2.    
    unfold transportb.    
    rewrite mor_disp_transportf_prewhisker.
    rewrite id_right_disp.
    unfold transportb.
    rewrite 2 transport_f_f.
    intermediate_path (transportf _ (idpath _ ) alpha).
    - apply maponpaths_2, homset_property.
    - apply idpath.
  Close Scope mor_disp.
  Defined.
  
  Lemma dispadjunction_hom_weq (c : C) (c' : C') (g : C⟦c, G c'⟧) (d : D c) (d' : D' c') :
      (d -->[g] GG _ d') ≃ (FF _ d -->[# F g · ε _] d').
  Proof.
    exists (homset_conj_inv g d d').
    apply (gradth _ (homset_conj g d d')).  
    - apply homset_conj_after_conj_inv.  
    - apply homset_conj_inv_after_conj.
  Defined.

End DispHomSetIso_from_Adjunction.


Lemma right_over_adj_preserves_cartesianness : is_cartesian_disp_functor GG.
Proof.
  unfold is_cartesian_disp_functor.
  intros c c' f d d' ff ff_cart.
  intros c'' g d'' h.
  unfold is_cartesian in ff_cart.
  assert (eq :  # F (g · # G f) · ε c = # F g · (ε c') · f).
  { rewrite functor_comp.
    rewrite <- assoc.
    cbn.
    set (nat_ε := nat_trans_ax ε _ _ f).
    cbn in nat_ε. rewrite nat_ε.
    rewrite assoc.
    apply idpath. }
  set (m := transportf _ eq (homset_conj_inv _ _ _ h)).
  apply (@iscontrweqb _
          (∑ gg : FF c'' d'' -->[ # F g · ε c'] d', (gg;; ff)%mor_disp = m)).
  (*    Search (_ -> weq (total2 _) (total2 _)). (* brilliant tip via Benedikt *) *)
  - apply (weqbandf (dispadjunction_hom_weq _ _ g _ _)).
    intro gg.
    cbn.
    unfold m.
    unfold homset_conj_inv.
    apply weqimplimpl.
    + intro p.
      rewrite <- p.
      rewrite disp_functor_comp. 
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite 2 assoc_disp_var.
      cbn.
      set (nat_εε := disp_nat_trans_ax εε ff).
      cbn in nat_εε. rewrite nat_εε.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite 3 transport_f_f.
      apply maponpaths_2, homset_property.
    
    + Open Scope mor_disp.
      intro p. cbn in p.
      (* this is tedious... *)
      set (equiv1 := homset_conj_after_conj_inv _ _ _ h).
      set (equiv2 := homset_conj_after_conj_inv _ _ _ (gg;; # GG ff)).
      unfold homset_conj, homset_conj_inv in equiv1, equiv2.
      rewrite <- equiv1.
      rewrite <- equiv2.
      rewrite (disp_functor_comp FF).
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite assoc_disp_var.
      cbn.
      set (nat_εε := disp_nat_trans_ax εε ff).
      cbn in nat_εε. rewrite nat_εε.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite assoc_disp.
      rewrite p.
      unfold transportb.
      rewrite 4 transport_f_f.
      rewrite disp_functor_transportf.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      apply maponpaths_2, homset_property.
    + apply homsets_disp.
    + apply homsets_disp.
  - apply ff_cart. 
Defined.

(* Proof strategy for right_over_adj_preserves_cartesianness:
   FF gg ; eps ; ff = FF h ; eps
   FF gg ; FF GG ff ; eps = FF h ; eps
   FF (gg ; GG ff) ; eps = FF h ; eps
   GG FF (gg ; GG ff) ; GG eps = GG FF h ; GG eps
   eta ; GG FF (gg ; GG ff) ; GG eps = eta ; GG FF h ; GG eps
   eta ; GG FF (gg ; GG ff) ; GG eps = h ; eta ; GG eps
   eta ; GG FF (gg ; GG ff) ; GG eps = h
   gg ; GG ff ; eta ; GG eps = h
   gg ; GG ff ; id = h
   gg ; GG ff = h *)

   

(** Path to happiness:

- construct homset-isomorphisms defined by a displayed adjunction;
  in particular,
  d -->[g] GG e  ≃   FF d -->[F g · counit _ ] e
- this equivalence is the equivalence in the first component of
   an equivalence between sigma types as occurring in def of [is_cartesian]
- use lemma saying that given an equivalence of types where one type is contractible,
  the other is, too
*)

End fix_disp_adjunction.
