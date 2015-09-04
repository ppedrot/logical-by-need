Require lambda.

Module Spec
  (Var : Orders.UsualOrderedType)
  (VSet : MSetInterface.SetsOn(Var))
  (Import Fresh : lambda.Fresh(Var)(VSet))
.

End Spec.
