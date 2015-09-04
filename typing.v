Require Import vars lambda.

Inductive type :=
| arrow : type -> type -> type
| prod : type -> type -> type
| quant : type -> type
| le : term -> term -> type.

Definition env := list (Var.t * type).

Inductive typing : env -> term -> type -> Prop :=.
