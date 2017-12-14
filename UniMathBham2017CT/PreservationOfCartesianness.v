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
  set (gamma := comp_disp (ηη _ _) (# GG beta)). 
  simpl in gamma.
  assert (equiv : η c · # G (# F g · ε c') = g) by
      exact (φ_adj_after_φ_adj_inv A g).
  exact (transportf _ equiv gamma).
  (*exact (transportf _ (φ_adj_after_φ_adj_inv A g) gamma).*)
  Defined.

(* Alternative symmetric definition : *)
  Definition homset_conj' {c : C} {c' : C'} (f : C'⟦F c, c'⟧)
            (d : D c) (d' : D' c') :
     (FF _ d -->[f] d') -> (d -->[η _ · #G f] GG _ d').
  Proof.
  intro beta.
  set (GGbeta := disp_functor_on_morphisms GG beta).
  exact (comp_disp (unit_over X _ _) GGbeta).
  Defined.

  Lemma homset_conj_inv_after_conj {c : C} {c' : C'} (g : C⟦c, G c'⟧)
        (d : D c) (d' : D' c')
        (beta : FF _ d -->[#F g · ε _] d') :
    homset_conj_inv _ _ _ (homset_conj g d d' beta) = beta. 
  Proof.
    Open Scope mor_disp.
    unfold homset_conj.
    unfold homset_conj_inv.
    rewrite (disp_functor_transportf).
    rewrite (mor_disp_transportf_postwhisker).
    rewrite (disp_functor_comp).
    unfold transportb.
    rewrite (mor_disp_transportf_postwhisker).
    rewrite (assoc_disp_var).
    simpl.
    rewrite 2 transport_f_f.
    intermediate_path ( transportf (mor_disp (FF c d) d')
    (assoc ((# F)%Cat (η c)) ((# F)%Cat ((# G)%Cat ((# F)%Cat g · ε c'))) (ε c') @
     cancel_postcomposition
       ((# F)%Cat (η c) · (# F)%Cat ((# G)%Cat ((# F)%Cat g · ε c')))
       ((# F)%Cat (η c · (# G)%Cat ((# F)%Cat g · ε c'))) 
       (ε c') (! functor_comp F (η c) ((# G)%Cat ((# F)%Cat g · ε c'))) @
     cancel_postcomposition ((# F)%Cat (η c · (# G)%Cat ((# F)%Cat g · ε c')))
       ((# F)%Cat g) (ε c') (maponpaths (# F)%Cat (φ_adj_after_φ_adj_inv A g)))
    (# FF (ηη c d);; ((# (disp_functor_composite GG FF) beta);; εε c' d'))).
    apply idpath.
    rewrite (disp_nat_trans_ax εε beta).
    simpl.
    unfold transportb.
    rewrite (mor_disp_transportf_prewhisker).
    rewrite (assoc_disp).
    rewrite (transport_f_f).
    rewrite (transport_f_b).
    assert (Tri : # FF (ηη c d);; εε (F c) (FF c d) = transportb _ (triangle_id_left_ad A c ) (id_disp _)).
    exact ((pr1 (pr2 X)) c d).
    simpl in Tri.
    rewrite Tri.
    unfold transportb.
    rewrite (mor_disp_transportf_postwhisker).
    rewrite id_left_disp.
    unfold transportb.
    rewrite transport_f_f.
    rewrite transport_f_f.
    intermediate_path (transportf _ (idpath _) beta).
    apply (Auxiliary.transportf_ext).
    apply proofirrelevance.
    Print has_homsets.
    apply (pr2 C').
    apply idpath.
Defined.
(*
  Lemma homset_conj_inv_after_conj' {c : C} {c' : C'} (f : C'⟦F c, c'⟧)
        (d : D c) (d' : D' c')
        (beta : FF _ d -->[f] d') :
    transportf _ (φ_adj_inv_after_φ_adj A f) (homset_conj_inv _ _ _ (homset_conj' f d d' beta)) = beta. 
  Proof.
    Open Scope mor_disp.
    unfold homset_conj.
    unfold homset_conj_inv.
    rewrite (disp_functor_transportf).
    rewrite (mor_disp_transportf_postwhisker).
    rewrite (disp_functor_comp).
    unfold transportb.
    rewrite (mor_disp_transportf_postwhisker).
    rewrite (assoc_disp_var).
    simpl.
    rewrite 2 transport_f_f.
    intermediate_path ( transportf (mor_disp (FF c d) d')
    (assoc ((# F)%Cat (η c)) ((# F)%Cat ((# G)%Cat ((# F)%Cat g · ε c'))) (ε c') @
     cancel_postcomposition
       ((# F)%Cat (η c) · (# F)%Cat ((# G)%Cat ((# F)%Cat g · ε c')))
       ((# F)%Cat (η c · (# G)%Cat ((# F)%Cat g · ε c'))) 
       (ε c') (! functor_comp F (η c) ((# G)%Cat ((# F)%Cat g · ε c'))) @
     cancel_postcomposition ((# F)%Cat (η c · (# G)%Cat ((# F)%Cat g · ε c')))
       ((# F)%Cat g) (ε c') (maponpaths (# F)%Cat (φ_adj_after_φ_adj_inv A g)))
    (# FF (ηη c d);; ((# (disp_functor_composite GG FF) beta);; εε c' d'))).
    apply idpath.
    rewrite (disp_nat_trans_ax εε beta).
    simpl.
    unfold transportb.
    rewrite (mor_disp_transportf_prewhisker).
    rewrite (assoc_disp).
    rewrite (transport_f_f).
    rewrite (transport_f_b).
    assert (Tri : # FF (ηη c d);; εε (F c) (FF c d) = transportb _ (triangle_id_left_ad A c ) (id_disp _)).
    exact ((pr1 (pr2 X)) c d).
    simpl in Tri.
    rewrite Tri.
    unfold transportb.
    rewrite (mor_disp_transportf_postwhisker).
    rewrite id_left_disp.
    unfold transportb.
    rewrite transport_f_f.
    rewrite transport_f_f.
    intermediate_path (transportf _ (idpath _) beta).
    apply (Auxiliary.transportf_ext).
    apply proofirrelevance.
    Print has_homsets.
    apply (pr2 C').
    apply idpath.
  Defined.
*)    
  Lemma homset_conj_after_conj_inv {c : C} {c' : C'} (g : C⟦c, G c'⟧)
        (d : D c) (d' : D' c')
        (alpha : d -->[g] GG _ d') :
    homset_conj _ _ _ (homset_conj_inv g d d' alpha) = alpha. 
  Proof.
    unfold homset_conj.    
    unfold homset_conj_inv.
    rewrite disp_functor_comp.
    simpl.
    unfold transportb.
    rewrite (mor_disp_transportf_prewhisker).
    rewrite (assoc_disp).
    (* Stuck again *)
    (* rewrite (disp_nat_trans_ax_var ηη alpha). *)
  Admitted.  

  Close Scope mor_disp.
  
  Lemma dispadjunction_hom_weq (c : C) (c' : C') (g : C⟦c, G c'⟧) (d : D c) (d' : D' c') :
      (d -->[g] GG _ d') ≃ (FF _ d -->[# F g · adjcounit A _] d').
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
  - rewrite functor_comp.
    rewrite <- assoc.
    intermediate_path (# F g · ((# (G ∙ F) f) · ε c)).
    apply idpath.
    rewrite (nat_trans_ax ε _ _ f).
    simpl.
    rewrite assoc.
    apply idpath.  
  - set (m := transportf _ eq (homset_conj_inv _ _ _ h)).
    set (H := ff_cart _ _ _ m).
    apply (@iscontrweqb _
            (∑ gg : FF c'' d'' -->[ # F g · ε c'] d', (gg;; ff)%mor_disp = m)).
    (* not sure best way to proceed here... *)

    rewrite (weqtopaths (dispadjunction_hom_weq _ _ g _ _)).
      (d -->[g] GG _ d') ≃ (FF _ d -->[# F g · adjcounit A _] d').

(c : C) (c' : C') (g : C⟦c, G c'⟧) (d : D c) (d' : D' c')


    apply eqweqmap.
    apply total2_paths2.
    Open Scope mor_disp.
    use tpair.
    intro x.
    exists (homset_conj_inv _ _ _ (pr1 x)).
    unfold m.
    rewrite <- (pr2 x).
    unfold homset_conj_inv.
    rewrite (disp_functor_comp).
    unfold transportb.
    rewrite (mor_disp_transportf_postwhisker).
    rewrite (assoc_disp_var).
    rewrite (assoc_disp_var).
    apply pathsinv0.
(*    (disp_functor_composite GG FF) *)
    intermediate_path (transportf (mor_disp (FF c'' d'') d) eq
    (transportf
       (mor_disp (FF c'' d'')
          ((disp_functor_identity D') c d))
       (cancel_postcomposition
          ((# F)%Cat g · (# F)%Cat ((# G)%Cat f))
          ((# F)%Cat (g · (# G)%Cat f)) 
          (ε c) (! functor_comp F g ((# G)%Cat f)))
       (transportf
          (mor_disp (FF c'' d'')
             ((disp_functor_identity D') c d))
          (assoc ((# F)%Cat g) ((# F)%Cat ((# G)%Cat f))
             (ε c))
          (# FF (pr1 x);; ((# (disp_functor_composite GG FF) ff);; εε c d))))).
    apply idpath.
    rewrite (disp_nat_trans_ax εε ff).
    simpl.
    unfold transportb.
    rewrite (mor_disp_transportf_prewhisker).
    rewrite 3 transport_f_f.
    apply (Auxiliary.transportf_ext).
    apply proofirrelevance.
    apply (pr2 C').
    simpl.
    
    intermediate_path ( transportf (mor_disp (FF c d) d')
    (assoc ((# F)%Cat (η c)) ((# F)%Cat ((# G)%Cat ((# F)%Cat g · ε c'))) (ε c') @
     cancel_postcomposition
       ((# F)%Cat (η c) · (# F)%Cat ((# G)%Cat ((# F)%Cat g · ε c')))
       ((# F)%Cat (η c · (# G)%Cat ((# F)%Cat g · ε c'))) 
       (ε c') (! functor_comp F (η c) ((# G)%Cat ((# F)%Cat g · ε c'))) @
     cancel_postcomposition ((# F)%Cat (η c · (# G)%Cat ((# F)%Cat g · ε c')))
       ((# F)%Cat g) (ε c') (maponpaths (# F)%Cat (φ_adj_after_φ_adj_inv A g)))
    (# FF (ηη c d);; ((# (disp_functor_composite GG FF) beta);; εε c' d'))).
    apply idpath.



(*    Focus 2.    *)
    exact H.


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
