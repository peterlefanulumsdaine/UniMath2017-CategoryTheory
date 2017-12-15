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
  set (gamma := comp_disp (ηη _ _) (# GG beta)). 
  simpl in gamma.
  assert (equiv : η c · # G (# F g · ε c') = g) by
      exact (φ_adj_after_φ_adj_inv A g).
  exact (transportf _ equiv gamma).
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
    rewrite disp_functor_transportf.
    rewrite mor_disp_transportf_postwhisker.
    rewrite disp_functor_comp.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite assoc_disp_var.
    simpl.
    rewrite 2 transport_f_f.
    set (nat := disp_nat_trans_ax εε beta).
    simpl in nat; rewrite nat; clear nat.
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite assoc_disp.
    unfold transportb.
    rewrite 2 transport_f_f.
    assert (triangle1 : # FF (ηη c d);; εε (F c) (FF c d) =
                        transportb _ (triangle_id_left_ad A c ) (id_disp _))
      by (exact ((pr1 (pr2 X)) c d)).
    simpl in triangle1.
    rewrite triangle1.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite id_left_disp.
    unfold transportb.
    rewrite 2 transport_f_f.
    intermediate_path (transportf _ (idpath _) beta).
    - apply maponpaths_2.
      apply proofirrelevance.
      apply (pr2 C').
    - apply idpath.
  Defined.
  
(*
  Lemma homset_conj_inv_after_conj' {c : C} {c' : C'} (f : C'⟦F c, c'⟧)
        (d : D c) (d' : D' c')
        (beta : FF _ d -->[f] d') :
    transportf _ (φ_adj_inv_after_φ_adj A f) (homset_conj_inv _ _ _ (homset_conj' f d d' beta)) = beta. 
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
    rewrite mor_disp_transportf_prewhisker.
    rewrite assoc_disp.
    unfold transportb.
    rewrite 2 transport_f_f.
    set (nat := disp_nat_trans_ax_var ηη alpha).
    simpl in nat; rewrite nat; clear nat.
    rewrite mor_disp_transportf_postwhisker.
    rewrite assoc_disp_var.
    rewrite 2 transport_f_f.
    assert (triangle2 : (ηη (G c') (GG c' d');; # GG (εε c' d')) =
       transportb _ (triangle_id_right_ad A c') (id_disp _)) by (exact (pr2 (pr2 X) c' d')).
    simpl in triangle2.
    rewrite triangle2.    
    unfold transportb.    
    rewrite mor_disp_transportf_prewhisker.
    rewrite id_right_disp.
    unfold transportb.
    rewrite 2 transport_f_f.
    intermediate_path (transportf _ (idpath _ ) alpha).
    - apply maponpaths_2.
      apply proofirrelevance.
      apply (pr2 C).
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
    simpl.
    set (nat := nat_trans_ax ε _ _ f).
    simpl in nat; rewrite nat.
    rewrite assoc.
    apply idpath. }
  set (m := transportf _ eq (homset_conj_inv _ _ _ h)).
  apply (@iscontrweqb _
          (∑ gg : FF c'' d'' -->[ # F g · ε c'] d', (gg;; ff)%mor_disp = m)).
  (*    Search (_ -> weq (total2 _) (total2 _)). (* brilliant tip via Benedikt *) *)
  + apply (weqbandf (dispadjunction_hom_weq _ _ g _ _)).
    intro gg.
    simpl.
    unfold m.
    unfold homset_conj_inv.
    apply weqimplimpl.
    * intro p.
      rewrite <- p.
      rewrite disp_functor_comp. 
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite 2 assoc_disp_var.
      simpl.
      set (nat := disp_nat_trans_ax εε ff).
      simpl in nat; rewrite nat.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite 3 transport_f_f.
      apply maponpaths_2.
      apply proofirrelevance.
      apply (pr2 C').
    
    * Open Scope mor_disp.
      intro p.
      rewrite assoc_disp_var in p.
      rewrite id_right_disp_var. 
      rewrite assoc_disp_var.
      assert (id_disp (GG c d) = transportf _ (triangle_id_right_ad A _ )
                                            ((ηη _ _ ;; (# GG) (εε _ _)) %mor_disp)).
      { apply transportf_transpose.
        rewrite (pr2 (pr2 X)).
        simpl.
        apply idpath. }
      (* this is tedious... *)
      assert (triangle2 : (ηη (G c) (GG c d);; # GG (εε c d)) =
                          transportb _ (triangle_id_right_ad A c) (id_disp _))
        by (exact (pr2 (pr2 X) c d)).
      simpl in triangle2.
      fold G in triangle2.
      rewrite (transportf_transpose _ _ _ (pathsinv0 triangle2)).
      set (nat := disp_nat_trans_ax_var εε ff).
      simpl in nat.
      simpl in p.
      rewrite nat in p.

   FF gg ; eps ; ff = FF h ; eps
   FF gg ; FF GG ff ; eps = FF h ; eps
   FF (gg ; GG ff) ; eps = FF h ; eps
   FF (gg ; GG ff) ; eps = FF h ; eps
   GG FF (gg ; GG ff) ; GG eps = GG FF h ; GG eps
   GG FF (gg ; GG ff) ; GG eps = GG FF h ; GG eps
   eta ; GG FF (gg ; GG ff) ; GG eps = eta ; GG FF h ; GG eps
   eta ; GG FF (gg ; GG ff) ; GG eps = h ; eta ; GG eps = h
   eta ; GG FF (gg ; GG ff) ; GG eps = h
   gg ; GG ff ; eta ; GG eps = h
   gg ; GG ff ; id = h
   gg ; GG ff = h

   
   
   GG FF gg ; GG eps ; GG ff = GG FF h ; GG eps
   GG FF gg ; GG (eps ; ff) =  GG FF h ; GG eps

   GG FF gg ; GG (FF GG ; eps) = GG FF h ; GG eps
   GG FF (gg ; ff) ; eps = GG FF h ; GG eps
   eps ; gg ; ff = GG FF h ; GG eps
   eps ; gg ; ff ; eta = GG FF h ; GG eps ; eta
   eps ; gg ; ff ; eta = GG FF h

    rewrite <- (disp_nat_trans_ax εε (# GG ff)).

(# FF gg;; εε c' d';; ff)%mor_disp =
  transportf (mor_disp (FF c'' d'') d) eq
    (# FF h;; εε c d)%mor_disp

(# FF gg;; GG FF ff; εε c' d')%mor_disp =

GG (# FF gg;; εε c' d';; ff)%mor_disp =
GG  transportf (mor_disp (FF c'' d'') d) eq
    (# FF h;; εε c d)%mor_disp

GG FF gg; GG eps ... ;; GG ff
g '' GG f



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
        set (H := ff_cart _ _ _ m).
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
