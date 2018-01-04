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
  
  Definition homset_conj_inv {c : C} {c' : C'} (g : C⟦c, G c'⟧) (d : D c) (d' : D' c') :
      (d -->[g] GG _ d') -> (FF _ d -->[#F g ·  ε _] d') :=
    λ alpha, comp_disp (# FF alpha) (εε _ _).

  Definition homset_conj' {c : C} {c' : C'} (f : C'⟦F c, c'⟧) (d : D c) (d' : D' c') :
     (FF _ d -->[f] d') -> (d -->[η _ · #G f] GG _ d') :=
    λ beta, comp_disp (ηη _ _) (# GG beta).

  Definition homset_conj'_inv {c : C} {c' : C'} (f : C'⟦F c, c'⟧) (d : D c) (d' : D' c') : 
    (d -->[η _ · #G f] GG _ d') -> (FF _ d -->[f] d').
  Proof.
    set (equiv := φ_adj_inv_after_φ_adj A f
                : # F (η c · # G f) · ε c' = f).
    exact (λ alpha, transportf _  equiv (homset_conj_inv _ _ _ alpha)).
  Defined.
  
  Definition homset_conj {c : C} {c' : C'} (g : C⟦c, G c'⟧) (d : D c) (d' : D' c') : 
    (FF _ d -->[#F g ·  ε _] d') -> (d -->[g] GG _ d').
  Proof.
    set (equiv := φ_adj_after_φ_adj_inv A g
                : η c · # G (# F g · ε c') = g).
    exact (λ beta, transportf _  equiv (homset_conj' _ _ _ beta)).
  Defined.
  

  Open Scope mor_disp.

  Lemma homset_conj_inv_natural_postcomp {c : C} {c' : C'} {g : C⟦c, G c'⟧} {c'' : C'}
      {f : C'⟦c', c''⟧} {d : D c} {d' : D' c'} {d'' : D' c''}
      (gg : d -->[g] GG _ d') (ff : d' -->[f] d'') :
    homset_conj_inv _ _ _ (gg ;; # GG ff)  =
    transportb _ (φ_adj_inv_natural_postcomp A _ _ g _ f) (homset_conj_inv _ _ _ gg ;; ff).
  Proof.
    unfold homset_conj_inv.
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
  Defined.

  Lemma homset_conj'_natural_precomp {c : C} {c' : C'} {f : C'⟦F c, c'⟧} {c'' : C}
        {k : C⟦c'', c⟧} {d : D c} {d' : D' c'} {d'' : D c''}
        (ff : FF _ d -->[f] d') (kk : d'' -->[k] d) :
    homset_conj' _ _ _ (# FF kk ;; ff) =
    transportb _ (φ_adj_natural_precomp A _ _ f _ k) (kk ;; homset_conj' _ _ _ ff).
  Proof.
    unfold homset_conj'.
    rewrite disp_functor_comp.
    unfold transportb.  
    rewrite mor_disp_transportf_prewhisker.
    rewrite 2 assoc_disp.
    cbn.
    set (nat_ηη := disp_nat_trans_ax_var ηη kk).
    cbn in nat_ηη. rewrite nat_ηη. clear nat_ηη.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite 3 transport_f_f.
    apply maponpaths_2, homset_property.   
  Defined.
  
  Lemma homset_conj_inv_after_conj {c : C} {c' : C'} {g : C⟦c, G c'⟧} (d : D c) {d' : D' c'}
        (beta : FF _ d -->[(#F)%Cat g · ε _] d') :
    homset_conj_inv _ _ _ (homset_conj _ _ _ beta) = beta.
  Proof.
    unfold homset_conj, homset_conj'.
    unfold homset_conj_inv.
    rewrite disp_functor_transportf.
    rewrite mor_disp_transportf_postwhisker.
    cbn.
    set (eq := homset_conj_inv_natural_postcomp (ηη c d) beta).
    unfold homset_conj_inv in eq.
    cbn in eq. rewrite eq.
    rewrite transport_f_b.
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
  Defined.
  
  
  Lemma homset_conj_inv_after_conj' {c : C} {c' : C'} (f : C'⟦F c, c'⟧)(d : D c) (d' : D' c')
        (beta : FF _ d -->[f] d') :
    transportf _ (φ_adj_inv_after_φ_adj A f) 
     (homset_conj_inv _ _ _ (homset_conj' f d d' beta)) = beta. 
  Proof.
    unfold homset_conj'.
    cbn.
    set (eq := homset_conj_inv_natural_postcomp (ηη c d) beta).
    cbn in eq. rewrite eq.
    unfold homset_conj_inv.
    cbn.
    rewrite transport_f_b.
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
  Defined.

  
  Lemma homset_conj_after_conj_inv {c : C} {c' : C'} {g : C⟦c, G c'⟧} {d : D c} (d' : D' c')
        (alpha : d -->[g] GG _ d') :
    homset_conj _ _ _ (homset_conj_inv _ _ _ alpha) = alpha. 
  Proof.
    unfold homset_conj.    
    unfold homset_conj_inv.
    cbn.
    set (eq := homset_conj'_natural_precomp (εε c' d') alpha).
    cbn in eq. rewrite eq.
    unfold homset_conj'.
    cbn.
    rewrite transport_f_b.
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
  Defined.

  Lemma homset_conj'_after_conj_inv {c : C} {c' : C'} {g : C⟦c, G c'⟧} {d : D c} (d' : D' c')
        (alpha : d -->[g] GG _ d') :
    transportf _ (φ_adj_after_φ_adj_inv A g) 
     (homset_conj' _ _ _ (homset_conj_inv g d d' alpha)) = alpha.
    unfold homset_conj_inv.
    cbn.
    set (eq := homset_conj'_natural_precomp (εε c' d') alpha).
    cbn in eq. rewrite eq.
    unfold homset_conj'.
    cbn.
    rewrite transport_f_b.
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
  Defined.

  Lemma homset_conj'_after_conj'_inv {c : C} {c' : C'} (f : C'⟦F c, c'⟧) (d : D c) (d' : D' c') 
    (alpha : d -->[η _ · (#G)%Cat f] GG _ d') :
        homset_conj' _ _ _ (homset_conj'_inv _ _ _ alpha) = alpha.
  Proof.
    unfold homset_conj', homset_conj'_inv.
    rewrite disp_functor_transportf.
    rewrite mor_disp_transportf_prewhisker.
    use (pathscomp0 _ (homset_conj'_after_conj_inv _ alpha)).
    apply maponpaths_2, homset_property.
  Defined.
  
    Close Scope mor_disp.
  
  Lemma dispadjunction_hom_weq (c : C) (c' : C') (g : C⟦c, G c'⟧) (d : D c) (d' : D' c') :
      (d -->[g] GG _ d') ≃ (FF _ d -->[# F g · ε _] d').
  Proof.
    exists (homset_conj_inv _ _ _).
    apply (gradth _ (homset_conj _ _ _)).  
    - apply homset_conj'_after_conj_inv.  
    - apply homset_conj_inv_after_conj.
  Defined.

  Lemma dispadjunction_hom_weq' (c : C) (c' : C') (f : C'⟦F c, c'⟧) (d : D c) (d' : D' c') :
       (FF _ d -->[f] d') ≃ (d -->[η _ · # G f] GG _ d').
  Proof.
    exists (homset_conj' _ _ _).
    apply (gradth _ (homset_conj'_inv _ _ _)).
    - apply homset_conj_inv_after_conj'.
    - apply homset_conj'_after_conj'_inv.
  Defined.
  
End DispHomSetIso_from_Adjunction.

Lemma right_over_adj_preserves_cartesianness : is_cartesian_disp_functor GG.
Proof.
  unfold is_cartesian_disp_functor.
  intros c c' f d d' ff ff_cart.
  intros c'' g d'' h.
  unfold is_cartesian in ff_cart.
  set (eq := φ_adj_inv_natural_postcomp A _ _ g _ f
           : # F (g · # G f) · ε c = # F g · (ε c') · f).
  Open Scope mor_disp.
  apply (@iscontrweqb _ (∑ gg, (gg;; ff) = transportf _ eq (homset_conj_inv _ _ _ h))).
  (*    Search (_ -> weq (total2 _) (total2 _)). (* brilliant tip via Benedikt *) *)
  - apply (weqbandf (dispadjunction_hom_weq _ _ g _ _)).
    intro gg.
    cbn.
    unfold homset_conj_inv.
    apply weqimplimpl.
    + intro p.
      rewrite <- p.
      cbn.
      set (eq2 := homset_conj_inv_natural_postcomp gg ff).
      unfold homset_conj_inv in eq2.
      cbn in eq2. rewrite eq2.
      rewrite transport_f_b.
      intermediate_path (transportf _ (idpath _ ) (# FF gg;; εε c' d';; ff)).
      * apply idpath.
      * apply maponpaths_2, homset_property.
    + intro p. cbn in p.
      (* this is tedious... *)
      set (equiv1 := homset_conj'_after_conj_inv _ h).
      set (equiv2 := homset_conj'_after_conj_inv _ (gg;; # GG ff)).
      unfold homset_conj', homset_conj_inv in equiv1, equiv2.
      rewrite <- equiv1.
      rewrite <- equiv2.
      cbn.
      set (eq2 := homset_conj_inv_natural_postcomp gg ff).
      unfold homset_conj_inv in eq2.
      cbn in eq2. rewrite eq2.
      rewrite p.
      rewrite transport_b_f.
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
