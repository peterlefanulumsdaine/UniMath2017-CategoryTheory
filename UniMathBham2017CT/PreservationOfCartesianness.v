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
  (*
  assert (equiv : η c · # G (# F g · ε c') = g) by
      exact (φ_adj_after_φ_adj_inv A g).
  exact (transportf _ equiv gamma). *)
  exact (transportf _ (φ_adj_after_φ_adj_inv A g) gamma).
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
    assert (S: # FF (ηη c d;; # GG beta) = transportb _ (functor_comp F _ _) (# FF (ηη c d);;# FF (# GG beta))) by (apply disp_functor_comp).
    intermediate_path (transportf (mor_disp (FF c d) (FF (G c') (GG c' d')))
    (maponpaths (# F)%Cat (φ_adj_after_φ_adj_inv A g)) 
    (transportb _ (functor_comp F _ _) (# FF (ηη c d);;# FF (# GG beta)));; εε c' d').
    - simpl.
      rewrite S.
      rewrite (disp_functor_comp FF (ηη c d) (# GG beta)). 
  Admitted.
    (* Stuck! Error: Found no subterm matching "# FF (ηη c d;; # GG beta)" in the current goal. *)
    (* Old attempts: 
    rewrite (disp_functor_comp FF (ηη c d) (# GG beta)). 
    assert (S: # FF (ηη c d;; # GG beta) = transportb _ (functor_comp F _ _) (# FF (ηη c d);;# FF (# GG beta))).
    apply (disp_functor_comp).
    rewrite S.
    rewrite (mor_disp_transportf_postwhisker).
    simpl.
    unfold transportb.
    rewrite (mor_disp_transportf_postwhisker).
    rewrite (assoc_disp_var).
    simpl.
    assert (S : # FF (# GG beta) = (# (disp_functor_composite GG FF) beta))
      by (apply idpath).
    rewrite S.
    rewrite (disp_nat_trans_ax εε beta).
    assert ((# FF (ηη c d);; (# FF (# GG beta);; εε c' d'))  = ((# FF (ηη c d);; (# (disp_functor_composite GG FF) beta) ;;  εε c' d'))). 
    apply idpath.
    Check (# FF (# GG beta)).
    unfold comp_disp.
    rewrite X0.
    rewrite (disp_nat_trans_ax εε beta). *)
    
(* Alternative symmetric definition : *)
    (* Definition homset_conj {c : C} {c' : C'} (f : C'⟦F c, c'⟧) *)
  (*           (d : D c) (d' : D' c') : *)
  (*    (FF _ d -->[f] d') -> (d -->[adjunit A _ · #G f] GG _ d'). *)
  (* Proof. *)
  (* intro beta. *)
  (* set (GGbeta := disp_functor_on_morphisms GG beta). *)
  (* exact (comp_disp (unit_over X _ _) GGbeta). *)
  (* Defined. *)

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
    Focus 2.    
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
