Require Import Omega Relations.
Require Import vars lambda typing.

Fixpoint comps (σ : list Var.t) : term :=
match σ with
| nil => refl
| cons x σ => comp (fvar x) (comps σ)
end.

Fixpoint forcing (σ : list Var.t) (ω : Var.t) t (Ht : STerm t) {struct Ht} : term.
Proof.
refine (
match Ht in STerm t return term with
| STerm_fvar x => fvar x @ fvar ω @ comps σ
| STerm_appl t u Ht Hu =>
  let (α, _) := fresh (VSet.union (fv u) (VSet.add ω (List.fold_right VSet.add VSet.empty σ))) in
  (forcing σ ω t Ht) @ λ[ω] λ[α] (forcing (cons α σ) ω u Hu)
| STerm_abst t Ht =>
  let (x, Hx) := fresh (VSet.union (fv t) (VSet.add ω (List.fold_right VSet.add VSet.empty σ))) in
  λ[x] (forcing σ ω _ (Ht x _))
| STerm_comp t u Ht Hu => comp (forcing σ ω t Ht) (forcing σ ω u Hu)
| STerm_refl => refl
end%term
).
clear - Hx; abstract (simplify_vset_hyps; intuition eauto).
Defined.

Local Ltac caseSTerm v :=
refine (match v with
| STerm_fvar x => _
| STerm_appl t u Ht Hu => _
| STerm_abst t Ht => _
| STerm_comp t u Ht Hu => _
| STerm_refl => _
end); unfold IDProp; trivial.

Lemma red_forcing_fvar : forall σ ω x Ht,
  forcing σ ω (fvar x) Ht = (fvar x @ fvar ω @ comps σ)%term.
Proof.
intros; caseSTerm Ht.
Qed.

Lemma red_forcing_abst : forall σ ω t Ht,
  { H |
  forcing σ ω (abst t) Ht =
  let (x, Hx) := fresh (VSet.union (fv t) (VSet.add ω (List.fold_right VSet.add VSet.empty σ))) in
  λ[x] (forcing σ ω (t << fvar x) (H x Hx))
  }%term.
Proof.
intros; caseSTerm Ht; cbn.
eexists; reflexivity.
Qed.

Lemma red_forcing_app : forall σ ω t u Htu,
  { H |
  forcing σ ω (appl t u) Htu =
  let (α, _) := fresh (VSet.union (fv u) (VSet.add ω (List.fold_right VSet.add VSet.empty σ))) in
  (forcing σ ω t (fst H)) @ λ[ω] λ[α] (forcing (cons α σ) ω u (snd H))
  }%term.
Proof.
intros; caseSTerm Htu; cbn.
exists (Ht, Hu); reflexivity.
Qed.

Lemma Term_forcing : forall σ ω t Ht, Term (forcing σ ω t Ht).
Proof.
intros σ ω t Ht; revert σ ω; induction Ht; intros σ ω; cbn in *; intuition eauto.
+ repeat constructor; induction σ; cbn; intuition eauto.
+ destruct fresh as [α Hα].
  repeat constructor; intuition eauto.
  eapply (Term_close (λ[α] (forcing (cons α σ) ω u _)) ω), Term_close; auto.
+ destruct fresh as [x Hx].
  apply Term_close; intuition.
Qed.

Lemma forcing_fv : forall σ ω t Ht x, VSet.In x (fv (forcing σ ω t Ht)) ->
  VSet.In x (VSet.union (fv t) (VSet.add ω (List.fold_right VSet.add VSet.empty σ))).
Proof.
intros σ ω t Ht; revert σ ω.
induction Ht; intros σ ω y Hy; cbn in *; simplify_vset_hyps; simplify_vset_goal; intuition eauto.
+ right; right; induction σ; cbn in *; simplify_vset_hyps; simplify_vset; intuition eauto.
+ destruct fresh as [α Hα]; cbn in *; simplify_vset; destruct Hy as [Hy|Hy].
  - apply IHHt1 in Hy; clear - Hy.
    simplify_vset; tauto.
  -
    do 2 (apply close_fv in Hy; destruct Hy as [? Hy]).
    apply IHHt2 in Hy.
    cbn in Hy; simplify_vset; tauto.
+ destruct fresh as [x Hx]; cbn in *.
  apply close_fv in Hy; destruct Hy as [? Hy].
  apply H in Hy; simplify_vset; intuition.
  apply FV.fv_open in H2; cbn in *; simplify_vset; intuition.
+ apply IHHt1 in H; simplify_vset; intuition eauto.
+ apply IHHt2 in H; simplify_vset; intuition eauto.
Qed.

Axiom F : False.

Lemma forcing_subst : forall t x r σ ω Ht Hr Hs,
  clos_refl_sym_trans _ red (forcing σ ω (t << r) Hs) [ forcing σ ω (t << fvar x) Ht | x := forcing σ ω r Hr].
Proof.
induction t; intros x r σ ω Ht Hr Hs; cbn in *.
+ repeat rewrite red_forcing_fvar; cbn.
  destruct F.
+ destruct Nat.eq_dec.
  - destruct F.
  - destruct F.
+ destruct F.
+ destruct (red_forcing_abst σ ω _ Ht) as [Ht' Hrw].
  rewrite Hrw; clear Hrw; destruct fresh as [y Hy].
  destruct (red_forcing_abst σ ω _ Hs) as [Hs' Hrw].
  rewrite Hrw; clear Hrw; destruct fresh as [z Hz].
  destruct F.
+ destruct F.
+ destruct F.
Qed.

Lemma forcing_red : forall t r σ ω Ht Hr,
  red t r -> red (forcing σ ω t Ht) (forcing σ ω r Hr).
Proof.
*)
