module IOu

-------- An IO type supporting possibly unique values

data IOu : Type* -> Type where
     MkIOu : IO a -> IOu a

(>>=) : {a,b: Type*} -> IOu a -> (a -> IOu b) -> IOu b
(>>=) (MkIOu x) k = MkIOu (do x' <- x
                              case k x' of
                                   MkIOu k' => k')

pure : {a : Type*} -> a -> IOu a
pure x = MkIOu (pure x)

run : IOu a -> IO a
run (MkIOu x) = x


