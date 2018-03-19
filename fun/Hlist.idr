module HList
  
data HList : Type where
  HNil : HList
  HCons : {a : Type} -> a -> HList -> HList
  
l : HList
l = (HCons 1 (HCons "foo" HNil))
