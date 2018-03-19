module Logic
  
%default total
  
data False : Type where
  
data Or a b = Left a | Right b
data And a b = UnAnd a b

proofA : (And a b -> c) -> (a -> b -> c)
proofA assump a b = assump (UnAnd a b)

proofB : ((Or a b) -> (Or c d) -> e) -> (a -> (e -> False) -> (c -> False))
proofB assump a ef c = ef (assump (Left a) (Left c))
