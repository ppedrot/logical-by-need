Require MSets NArith Wellfounded.
Require Import Program Setoid Morphisms BinNat Relations.

Module Type Fresh
  (Var : Orders.UsualOrderedType)
  (VSet : MSetInterface.SetsOn(Var)).

Parameter fresh : forall s : VSet.t, {v | ~ VSet.In v s}.

End Fresh.


Module Spec
  (Var : Orders.UsualOrderedType)
  (VSet : MSetInterface.SetsOn(Var))
  (Import Fresh : Fresh(Var)(VSet))
.

Module Import VSetFacts := MSetFacts.WFactsOn(Var)(VSet).

Inductive term :=
| fvar : Var.t -> term
| bvar : nat -> term
| appl : term -> term -> term
| abst : term -> term
| comp : term -> term -> term
| refl : term.

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
| comp t u => comp (open t n r) (open u n r)
| refl => refl
end.

Notation "t << u" := (open t 0 u) (at level 50, left associativity).

Inductive Term : term -> Prop :=
| Term_fvar : forall x, Term (fvar x)
| Term_appl : forall t u, Term t -> Term u -> Term (appl t u)
| Term_abst : forall L t,
  (forall x, ~ VSet.In x L -> Term (t << fvar x)) ->
  Term (abst t)
| Term_comp : forall t u, Term t -> Term u -> Term (comp t u)
| Term_refl : Term refl
.

Fixpoint subst (t : term) (x : Var.t) (r : term) :=
match t with
| fvar y => if Var.eq_dec x y then r else fvar y
| bvar m => bvar m
| appl t u => appl (subst t x r) (subst u x r)
| abst t => abst (subst t x r)
| comp t u => comp (subst t x r) (subst u x r)
| refl => refl
end.

Notation "[ t | x := r ]" := (subst t x r).

Inductive red : term -> term -> Prop :=
| red_beta : forall t u, red (appl (abst t) u) (t << u)
| red_appl_l : forall t u r, red t r -> red (appl t u) (appl r u)
| red_appl_r : forall t u r, red u r -> red (appl t u) (appl t r).

Definition lift1 x α t := subst t x (λ λ (fvar x @ bvar 1 @ (comp (bvar 0) α))).

Fixpoint lift σ α t {struct t} := VSet.fold (fun x t => lift1 x α t) σ t.

Fixpoint forcing (σ : VSet.t) ω t {struct t} : term :=
match t with
| bvar n => bvar n
| fvar x => fvar x @ fvar ω @ refl
| appl t u => t
| abst t => t
| _ => t
end.

