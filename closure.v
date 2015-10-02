Require Import vars lambda.

Inductive closure : term -> Prop :=
| closure_bvar : closure (bvar 0)
| closure_cons : forall x t C1 C2,
  closure C1 -> closure C2 ->
  closure ((C1 << (λ[x] (C2 << (fvar x)))) @ t).
