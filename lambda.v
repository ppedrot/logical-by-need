Require Import Omega Relations vars.

Inductive term :=
| fvar : Var.t -> term
| bvar : nat -> term
| appl : term -> term -> term
| abst : term -> term
.

Bind Scope trm_scope with term.
Delimit Scope trm_scope with term.

Notation "'λ' t" := (abst t) (at level 80, t at level 0, format "'λ'  t") : trm_scope.
Notation "t @ u" := (appl t u) (at level 20, left associativity) : trm_scope.

Fixpoint open (t : term) (n : nat) (r : term) :=
match t with
| fvar x => fvar x
| bvar m => if PeanoNat.Nat.eq_dec m n then r else bvar m
| appl t u => appl (open t n r) (open u n r)
| abst t => abst (open t (S n) r)
end.

Notation "t << u" := (open t 0 u) (at level 50, left associativity).

Inductive Term : term -> Prop :=
| Term_fvar : forall x, Term (fvar x)
| Term_appl : forall t u, Term t -> Term u -> Term (appl t u)
| Term_abst : forall L t,
  (forall x, ~ VSet.In x L -> Term (t << fvar x)) ->
  Term (abst t)
.

Hint Constructors Term.

Fixpoint subst (t : term) (x : Var.t) (r : term) :=
match t with
| fvar y => if Var.eq_dec x y then r else fvar y
| bvar m => bvar m
| appl t u => appl (subst t x r) (subst u x r)
| abst t => abst (subst t x r)
end.

Notation "[ t | x := r ]" := (subst t x r).

Fixpoint fv (t : term) : VSet.t :=
match t with
| fvar y => VSet.add y VSet.empty
| bvar m => VSet.empty
| appl t u => VSet.union (fv t) (fv u)
| abst t => fv t
end.

Instance Nominal_term : forall t, Nominal term t (fv t).

Fixpoint close (t : term) (x : Var.t) (n : nat) :=
match t with
| fvar y => if Var.eq_dec x y then bvar n else fvar y
| bvar m => bvar m
| appl t u => appl (close t x n) (close u x n)
| abst t => abst (close t x (S n))
end.

Notation "λ[ x ] t" := (λ (close t x 0))%term (at level 80, t at level 0, format "λ[ x ] t") : trm_scope.

Ltac pick x :=
  gather_ ltac:(fun s =>
  pose (x := fresh s);
  cbn [List.fold_left] in x;
  let H := fresh in
  destruct x as [x H];
  simplify_vset_hyp H
  ).

Ltac gather L :=
  gather_ ltac:(fun s =>
  pose (L := s);
  cbn [fv List.fold_left] in L).

Inductive red : term -> term -> Prop :=
| red_beta : forall t u, red (appl (abst t) u) (t << u)
| red_appl_l : forall t u r, red t r -> red (appl t u) (appl r u)
| red_appl_r : forall t u r, red u r -> red (appl t u) (appl t r).

Definition betaeq : relation term := clos_refl_sym_trans _ red.

Notation "t ≡β u" := (betaeq t u) (at level 70).

Instance Equivalence_betaeq : RelationClasses.Equivalence betaeq.
Proof.
split; apply clos_rst_is_equiv.
Qed.

Lemma open_inj : forall t n1 n2 r1 r2, n1 <> n2 ->
  open t n1 r1 = open (open t n1 r1) n2 r2 -> t = open t n2 r2.
Proof.
induction t; intros n1 n2 r1 r2 Hn Hrw; cbn in *; try inversion Hrw; f_equal;
try solve [intuition eauto]; cbn in *.
repeat (destruct PeanoNat.Nat.eq_dec; cbn in *); first [omega|intuition].
Qed.

Lemma Term_open_idem : forall t n r,
  Term t -> open t n r = t.
Proof.
intros t n r Ht; revert n.
induction Ht; intros n; cbn in *; f_equal; intuition eauto.
pick x; erewrite <- (open_inj _ 0); [|omega|symmetry]; intuition eauto.
Qed.

Lemma open_subst_trans : forall t n x r,
  ~ VSet.In x (fv t) -> [ open t n (fvar x) | x := r ] = open t n r.
Proof.
intros t.
induction t; intros; cbn in *; simplify_vset_hyps; f_equal; intuition eauto.
+ destruct eq_dec; intuition eauto.
+ destruct Nat.eq_dec; cbn; [destruct eq_dec|]; intuition.
Qed.

Lemma Term_subst_distr : forall t n u x r, Term r ->
  [ open t n u | x := r ] = open [t | x := r] n [u | x := r].
Proof.
intros t.
induction t; intros; cbn in *; simplify_vset_hyps; f_equal; intuition eauto.
+ destruct eq_dec; intuition eauto.
  rewrite Term_open_idem; now intuition.
+ destruct Nat.eq_dec; cbn; intuition.
Qed.

Lemma Term_subst_idem : forall t x r, ~ VSet.In x (fv t) -> [ t | x := r ] = t.
Proof.
induction t; intros; cbn in *; simplify_vset_hyps; f_equal; intuition eauto.
+ destruct eq_dec; intuition eauto.
Qed.

Lemma subst_comm : forall t n u x r, Term r -> ~ VSet.In x (fv u) ->
  [ open t n u | x := r ] = open [t | x := r] n u.
Proof.
intros.
rewrite <- (Term_subst_idem u x r) at 2; [|assumption].
apply Term_subst_distr; assumption.
Qed.

Lemma Term_subst_compat : forall t x r,
  Term t -> Term r -> Term [t | x := r].
Proof.
intros t x r Ht Hr; induction Ht; cbn; try solve [intuition eauto].
+ destruct eq_dec; subst; intuition.
+ gather L'; apply Term_abst with L'; intros; unfold L' in *.
  simplify_vset_hyps; rewrite <- subst_comm; cbn in *; intuition eauto.
  simplify_vset_hyps; intuition eauto.
Qed.

Lemma open_comm : forall t n1 n2 r1 r2, Term r1 -> Term r2 -> n1 <> n2 -> 
  open (open t n1 r1) n2 r2 = open (open t n2 r2) n1 r1.
Proof.
induction t; intros; cbn in *; try solve [f_equal; intuition eauto].
repeat (destruct Nat.eq_dec; cbn); try rewrite Term_open_idem; (omega || intuition eauto).
Qed.

Lemma close_open : forall t x, ~ VSet.In x (fv t) -> close (t << fvar x) x 0 = t.
Proof.
intros t; generalize 0.
induction t; intros; cbn in *; simplify_vset_hyps; f_equal; intuition eauto.
+ destruct eq_dec; cbn; intuition.
+ destruct Nat.eq_dec; cbn; intuition.
  destruct eq_dec; intuition eauto.
Qed.

Lemma close_fv_from : forall t x y n, VSet.In x (fv (close t y n)) -> VSet.In x (fv t).
Proof.
induction t; intros; cbn in *; simplify_vset; intuition eauto.
destruct eq_dec; cbn in *; simplify_vset_hyps; intuition.
Qed.

Lemma close_not_fv : forall t x n, ~ VSet.In x (fv (close t x n)).
Proof.
induction t; intros; cbn in *; simplify_vset; intuition eauto.
destruct eq_dec; cbn in *; simplify_vset_hyps; intuition.
Qed.

Lemma close_fv : forall t x y n, VSet.In x (fv (close t y n)) -> x <> y /\ VSet.In x (fv t).
Proof.
intros; split; [intros ->; eelim close_not_fv; eauto|eapply close_fv_from; eauto].
Qed.

Lemma open_close : forall t x (n : nat) r, Term r -> ~ VSet.In x (fv r) ->
  open (close t x n) n r = [open t n r | x := r].
Proof.
intros t; induction t; intros y m r Hr Hx; cbn in *; f_equal; intuition eauto.
+ destruct eq_dec; cbn; intuition.
  destruct Nat.eq_dec; intuition congruence.
+ destruct Nat.eq_dec; intuition.
  symmetry; apply Term_subst_idem; intuition.
Qed.

Lemma Term_close : forall t x, Term t -> Term (λ[x] t).
Proof.
intros t x Ht; gather L.
apply Term_abst with L; intros; unfold L in *; simplify_vset_hyps.
rewrite open_close; cbn; simplify_vset_goal; intuition.
rewrite Term_open_idem; intuition.
apply Term_subst_compat; intuition.
Qed.

Lemma close_subst : forall t x y n,
  ~ VSet.In y (fv t) ->
  close t x n = close [t | x := fvar y] y n.
Proof.
induction t; intros x y m Hy; cbn in *; simplify_vset; f_equal; intuition eauto.
destruct eq_dec; cbn in *; destruct eq_dec; intuition.
Qed.

Fixpoint is_Term t (n : nat) {struct t} : bool :=
match t with
| fvar x => true
| bvar m => m <? n
| appl t u => is_Term t n && is_Term u n
| abst t => is_Term t (S n)
end.

Inductive OTerm n : term -> Type :=
| OTerm_fvar : forall x : Var.t, OTerm n (fvar x)
| OTerm_bvar : forall m, m < n -> OTerm n (bvar m)
| OTerm_appl : forall t u : term, OTerm n t -> OTerm n u -> OTerm n (t @ u)
| OTerm_abst : forall (t : term), (OTerm (S n) t) -> OTerm n (λ t)
.

Fixpoint opens t n r :=
match t with
| fvar x => fvar x
| bvar m =>
  let r := if lt_dec m n then None else List.nth_error r (m - n) in
  match r with None => bvar m | Some r => r end
| (t0 @ u)%term => (opens t0 n r @ opens u n r)%term
| (λ t0)%term => (λ (opens t0 (S n) r))%term
end.

Fixpoint openr t n rs :=
match rs with
| nil => t
| cons r rs => open (openr t (S n) rs) n r
end.

Fixpoint openl t n rs :=
match rs with
| nil => t
| cons r rs => openl (open t n r) (S n) rs
end.

Lemma opens_open_l : forall t n r rs,
  List.Forall Term rs ->
  opens t n (cons r rs) = open (opens t (S n) rs) n r.
Proof.
induction t; intros m r rs Hrs; cbn in *; try solve [f_equal; intuition eauto].
destruct lt_dec.
+ destruct lt_dec; [|exfalso; omega].
  cbn; destruct Nat.eq_dec; [exfalso; omega|trivial].
+ destruct lt_dec.
  - replace (n - m) with 0 by omega; cbn.
    destruct Nat.eq_dec; [reflexivity|omega].
  - replace (n - m) with (S (n - S m)) by omega; cbn in *.
    case_eq (List.nth_error rs (n - S m)); cbn.
    { intros; symmetry; apply Term_open_idem.
      eapply List.Forall_forall in Hrs; [eassumption|].
      eapply List.nth_error_In; eassumption. }
    { intros; destruct Nat.eq_dec; [omega|trivial]. }
Qed.


Lemma opens_openr : forall t n rs, List.Forall Term rs -> opens t n rs = openr t n rs.
Proof.
intros t n rs; revert t n; induction rs as [|r rs]; intros t n Hrs; cbn in *.
+ clear; revert n; induction t; intros m; cbn; try solve [f_equal; intuition eauto].
  destruct lt_dec; [reflexivity|].
  destruct (n - m); reflexivity.
+ rewrite <- IHrs; [|inversion Hrs; assumption].
  rewrite opens_open_l; [|inversion Hrs; assumption].
  reflexivity.
Qed.

Lemma opens_inj : forall t n1 n2 r rs, n1 < n2 ->
  open t n1 r = opens (open t n1 r) n2 rs -> t = opens t n2 rs.
Proof.
induction t; intros n1 n2 r rs Hn Hrw; cbn in *; try solve [f_equal; try injection Hrw; intuition eauto].
+ destruct lt_dec; cbn in *; [reflexivity|].
  destruct Nat.eq_dec; [omega|].
  cbn in *; destruct lt_dec; [omega|assumption].
+ injection Hrw; clear Hrw; intros Hrw; f_equal.
  eapply IHt; [|eassumption]; omega.
Qed.

Lemma Term_opens_idem : forall t n r,
  Term t -> opens t n r = t.
Proof.
intros t n r Ht; revert n r; induction Ht; intros n r; cbn in *; try solve [f_equal; intuition eauto].
f_equal; pick x; symmetry; eapply (opens_inj _ 0); [omega|symmetry].
intuition eauto.
Qed.

(*
Lemma opens_app : forall t n rs1 rs2,
  List.Forall Term rs1 ->
  opens (opens t (n + List.length rs1) rs2) n rs1 = opens t n (app rs1 rs2).
Proof.
induction t; intros m rs1 rs2 Hrs1; cbn in *; try solve [f_equal; intuition eauto].
+ destruct lt_dec; cbn in *.
  - destruct lt_dec; [reflexivity|].
    rewrite List.nth_error_app1; [reflexivity|omega].
  - destruct lt_dec; [omega|].
    rewrite List.nth_error_app2; [|omega].
    replace (n - (m + length rs1)) with (n - m - length rs1) by omega.
    case_eq (List.nth_error rs2 (n - m - length rs1)).
    { intros r Hr; apply Term_opens_idem; [eapply List.nth_error_In, List.Forall_forall in Hr|].
Qed.
*)

(* Lemma opens_open_r : forall t n r rs,
  List.Forall Term rs ->
  opens t n (app rs (cons r nil)) = open (opens t (S n) rs) n r.
Proof.
induction t; intros m r rs Hrs; cbn in *; try solve [f_equal; intuition eauto].
destruct lt_dec.
+ destruct lt_dec; [|exfalso; omega].
  cbn; destruct Nat.eq_dec; [exfalso; omega|trivial].
+ destruct lt_dec.
  - replace (n - m) with 0 by omega; cbn.
    destruct Nat.eq_dec; [reflexivity|omega].
  - replace (n - m) with (S (n - S m)) by omega; cbn in *.
    case_eq (List.nth_error rs (n - S m)); cbn.
    { intros; symmetry; apply Term_open_idem.
      eapply List.Forall_forall in Hrs; [eassumption|].
      eapply List.nth_error_In; eassumption. }
    { intros; destruct Nat.eq_dec; [omega|trivial]. }
Qed.
 *)

Lemma opens_open_comm : forall t n m r rs,
  n < m -> List.Forall Term rs -> Term r ->
  open (opens t m rs) n r = opens (open t n r) m rs.
Proof.
induction t; intros m m' r rs Hm Hrs Hr; cbn in *; try solve [f_equal; intuition eauto].
+ destruct lt_dec; cbn in *.
  - destruct Nat.eq_dec; cbn; [|].
    { symmetry; apply Term_opens_idem; assumption. }
    { destruct lt_dec; [reflexivity|omega]. }
  - destruct Nat.eq_dec; cbn in *; [omega|].
    destruct lt_dec; [omega|].
    case_eq (List.nth_error rs (n - m')); cbn.
    { intros t Ht; apply Term_open_idem; eapply List.nth_error_In, List.Forall_forall in Ht; eassumption. }
    { intros _; destruct Nat.eq_dec; [omega|reflexivity]. }
+ f_equal; apply IHt; try (assumption || omega).
Qed.

Lemma Term_abst_weak : forall L t n x,
  (forall y, ~ VSet.In y L -> Term (open t n (fvar y))) ->
  ~ VSet.In x (fv t) -> Term (open t n (fvar x)).
Proof.
intros; pick y.
erewrite <- (open_subst_trans _ _ y); [|intuition eauto].
apply Term_subst_compat; intuition eauto.
Qed.

Lemma OTerm_Term_n : forall n t (r : list Var.t),
  List.length r = n ->
  OTerm n t -> Term (opens t 0 (List.map fvar r)).
Proof.
intros n t r Hr Ht; revert r Hr.
induction Ht; intros r Hr; cbn; try solve [intuition eauto].
+ replace (m - 0) with m by omega.
  case_eq (List.nth_error (List.map fvar r) m); cbn.
  - intros t Ht; apply List.nth_error_In in Ht.
    clear - Ht; induction r; cbn in *; intuition.
    subst t; intuition.
  - intros H; apply List.nth_error_None in H; rewrite List.map_length in H; omega.
+ gather L; apply Term_abst with L; intros x Hx.
  assert (HT : List.Forall Term (List.map fvar r)).
  { clear; induction r; cbn in *; constructor; intuition eauto. }
  rewrite <- opens_open_l; [|intuition].
  apply (IHHt (cons x r)); cbn; congruence.
Qed.

Lemma OTerm_Term_0 : forall t, OTerm 0 t -> Term t.
Proof.
intros t Ht.
replace t with (opens t 0 nil); [apply (OTerm_Term_n 0 _ nil); intuition|].
clear; generalize 0; induction t; intros m; cbn in *; try solve [f_equal; intuition eauto].
destruct lt_dec; [reflexivity|].
destruct (n - m); cbn; reflexivity.
Qed.

Lemma is_Term_OTerm : forall t n, is_Term t n = true -> OTerm n t.
Proof.
induction t; intros m Ht; cbn in *;
try apply Bool.andb_true_iff in Ht;
try solve [constructor; intuition eauto].
destruct m; [congruence|].
constructor; apply leb_complete in Ht.
omega.
Qed.

Lemma OTerm_is_Term : forall t n, OTerm n t -> is_Term t n = true.
Proof.
intros t n Ht; induction Ht; cbn in *;
try apply Bool.andb_true_iff;
try solve [intuition eauto].
destruct n; [omega|].
apply leb_correct; omega.
Qed.

Lemma Term_OTerm_0 : forall t, Term t -> OTerm 0 t.
Proof.
intros t Ht; apply is_Term_OTerm; induction Ht; cbn in *;
try apply Bool.andb_true_iff; intuition eauto.
pick x; assert (Hx : is_Term (t << fvar x) 0 = true) by intuition eauto.
revert Hx; clear.
generalize 0; induction t; intros m Ht; cbn in *;
try apply Bool.andb_true_iff; try apply Bool.andb_true_iff in Ht;
first [reflexivity|intuition|idtac].
destruct Nat.eq_dec; cbn in *.
+ apply leb_correct; omega.
+ destruct m; [discriminate|].
  apply leb_correct; apply leb_complete in Ht; omega.
Qed.

Inductive STerm : term -> Type :=
| STerm_fvar : forall x, STerm (fvar x)
| STerm_appl : forall t u, STerm t -> STerm u -> STerm (appl t u)
| STerm_abst : forall t,
  (forall x, ~ VSet.In x (fv t) -> STerm (t << fvar x)) ->
  STerm (abst t)
.

Hint Constructors STerm.

Lemma OTerm_STerm_n : forall n t (r : list Var.t),
  List.length r = n ->
  OTerm n t -> STerm (opens t 0 (List.map fvar r)).
Proof.
intros n t r Hr Ht; revert r Hr.
induction Ht; intros r Hr; cbn; try solve [intuition eauto].
+ replace (m - 0) with m by omega.
  case_eq (List.nth_error (List.map fvar r) m); cbn.
  - intros t Ht; apply List.nth_error_In in Ht.
    assert (H : exists x, t = fvar x).
    { clear - Ht; induction r; cbn in *; intuition eauto. }
    destruct t; try (exfalso; destruct H; congruence).
    constructor.
  - intros H; apply List.nth_error_None in H; rewrite List.map_length in H; omega.
+ apply STerm_abst; intros x Hx.
  assert (HT : List.Forall Term (List.map fvar r)).
  { clear; induction r; cbn in *; constructor; intuition eauto. }
  rewrite <- opens_open_l; [|intuition].
  apply (IHHt (cons x r)); cbn; congruence.
Qed.

Lemma OTerm_STerm_0 : forall t, OTerm 0 t -> STerm t.
Proof.
intros t Ht.
replace t with (opens t 0 nil); [apply (OTerm_STerm_n 0 _ nil); intuition|].
clear; generalize 0; induction t; intros m; cbn in *; try solve [f_equal; intuition eauto].
destruct lt_dec; [reflexivity|].
destruct (n - m); cbn; reflexivity.
Qed.

Module FV.

Lemma fv_open : forall x t n r,
  VSet.In x (fv (open t n r)) -> VSet.In x (fv t) \/ VSet.In x (fv r).
Proof.
intros x t; revert x; induction t; intros; cbn in *; simplify_vset; intuition eauto.
+ destruct Nat.eq_dec; cbn in *; simplify_vset; intuition.
+ apply IHt1 in H0; intuition eauto.
+ apply IHt2 in H0; intuition eauto.
Qed.

End FV.
