-- ------------------------------------------------------------ [ Protocol.idr ]
-- An effectful implementation of protocols.
-- --------------------------------------------------------------------- [ EOH ]
module Protocol

data SubList : List a -> List a -> Type where
     SubNil : SubList [] []
     Keep   : SubList xs ys -> SubList (x :: xs) (x :: ys)
     Drop   : SubList xs ys -> SubList xs (x :: ys)

data Elem : a -> List a -> Type where
     Here  : Elem x (x :: xs)
     There : Elem x xs -> Elem x (y :: xs)

isElemSyn : (x : a) -> (xs : List a) -> Maybe (Elem x xs)
isElemSyn x [] = Nothing
isElemSyn x (y :: xs) with (prim__syntactic_eq _ _ x y)
  isElemSyn x (y :: xs) | Nothing = pure $ There !(isElemSyn x xs)
  isElemSyn x (x :: xs) | (Just Refl) = pure Here

syntax IsOK = tactics { search 100; }

-- ------------------------------------------------- [ Protocol Definition ]

||| Checks if a send is valid, and computes the return type
|||
||| The return type tells us how the rest of the protocol can depend on
||| the value that was trasmitted. If there are only two participants,
||| clearly they both know the value, so it is safe to depend on it.
||| Otherwise, we can't depend on it, so return ().
data SendOK : (transmitted : Type) -> 
              (from : proc) -> 
              (to : proc) -> 
              (participants : List proc) -> 
              (continuation : Type) -> Type where
     SendLR : SendOK a x y [x, y] a
     SendRL : SendOK a x y [y, x] a
     SendGhost : Elem x xs -> Elem y xs -> SendOK a x y xs ()

||| Definition of protocol actions. 
data Protocol : List proc -> Type -> Type where
     Initiate : (client : proc) -> (server : proc) ->
                {auto prfc : Elem client xs} ->
                {auto prfs : Elem server xs} ->
                Protocol [client, server] () -> Protocol xs ()

     ||| Send data from one procipal to another.
     |||
     ||| @from The message originator.
     ||| @to   The message recipient.
     ||| @a    The type of the message to be sent.
     Send' : (from : proc) -> (to : proc) -> (a : Type) ->
             (prf : SendOK a from to xs b) -> Protocol xs b
     
     ||| To support do-notation in protocols.
     (>>=) : Protocol xs a -> (a -> Protocol xs b) -> Protocol xs b

     ||| Call a sub-protocol with a subset of the participants
     With' : (xs : List a) -> SubList xs ys -> Protocol xs () -> Protocol ys ()

     Rec : Inf (Protocol xs a) -> Protocol xs a  
     pure : a -> Protocol xs a

serverLoop : (c : proc) -> Protocol [c, s] () -> Protocol [c, s] ()
serverLoop c {s} proto = Initiate c s $ do
                           proto
                           Rec (serverLoop c proto)

||| Signify the end of a protocol.
Done : Protocol xs ()
Done = pure ()

||| Send data from one procipal to another.
|||
||| @from The message originator.
||| @to   The message recipient.
||| @a    The type of the message to be sent.       
Send : (from : proc) -> (to : proc) -> (a : Type) ->
       {auto prf : SendOK a from to xs b} ->
       Protocol xs b
Send from to a {prf} = Send' from to a prf

Call : {auto prf : SubList xs ys} -> Protocol xs () -> Protocol ys ()
Call {prf} x = With' _ prf x 

With : (xs : List a) -> {auto prf : SubList xs ys} -> 
       Protocol xs () -> Protocol ys ()
With xs {prf} x = With' xs prf x 

-- Syntactic Sugar for specifying protocols.
syntax [from] "==>" [to] "|" [t] = Send from to t

data Actions : Type where
     DoListen  : (client : proc) -> Actions -> Actions

     DoSend    : (dest : proc) -> (x : Type) -> (x -> Actions) -> Actions
     DoRecv    : (src : proc) -> (x : Type) -> (x -> Actions) -> Actions

     DoRec     : Inf Actions -> Actions
     End       : Actions

data Valid : p -> List (p, chan) -> Type where
     First : .{x : p} -> .{xs : List (p, chan)} -> {c : chan} ->
             Valid x ((x, c) :: xs)
     Later : .{x : p} -> .{xs : List (p, chan)} ->
             Valid x xs -> Valid x (y :: xs)

infix 5 :=

(:=) : p -> chan -> (p, chan)
(:=) x c = (x, c)

lookup : (xs : List (p, chan)) -> Valid x xs -> chan
lookup ((x, c) :: ys) First = c
lookup (y :: ys) (Later x) = lookup ys x

remove : (xs : List (p, chan)) -> Valid x xs -> List (p, chan)
remove ((x, c) :: ys) First = ys
remove (y :: ys) (Later x) = y :: remove ys x

-- total
-- %reflection -- otherwise matching SendGhost not allowed!
mkProcess : (x : proc) -> Protocol xs ty -> 
            {auto prf : Elem x xs} ->
            (ty -> Actions) -> Actions

mkProcess x (Initiate client server p) k with (prim__syntactic_eq _ _ x server)
  mkProcess x (Initiate client server p) k | Nothing = k () 
  mkProcess x (Initiate client x p) k | (Just Refl) = DoListen client (mkProcess x p k)

mkProcess x (Send' from to ty (SendGhost y z)) k with (prim__syntactic_eq _ _ x from)
  mkProcess x (Send' from to ty (SendGhost y z)) k | Nothing with (prim__syntactic_eq _ _ x to)
    mkProcess x (Send' from to ty (SendGhost y z)) k | Nothing | Nothing = k () 
    mkProcess x (Send' from to ty (SendGhost y z)) k | Nothing | (Just w) = DoRecv from ty (\x => k ())
  mkProcess x (Send' from to ty (SendGhost y z)) k | (Just w) = DoSend to ty (\x => k ()) 

mkProcess {xs = [from,to]} x (Send' from to ty SendLR) k with (prim__syntactic_eq _ _ x from)
      | Nothing = DoRecv from ty k 
      | (Just y) = DoSend to ty k
mkProcess {xs = [to,from]} x (Send' from to ty SendRL) k with (prim__syntactic_eq _ _ x from)
      | Nothing = DoRecv from ty k 
      | (Just y) = DoSend to ty k

mkProcess x (With' xs sub prot) k with (isElemSyn x xs)
      | Nothing = k () 
      | (Just prf) = mkProcess x prot k
mkProcess x (y >>= f) k = mkProcess x y (\cmd => mkProcess x (f cmd) k)
mkProcess x (Rec p) k = DoRec (mkProcess x p k)
mkProcess x (pure y) k = k y

protoAs : (x : proc) -> Protocol xs () -> {auto prf : Elem x xs} -> Actions
protoAs x p = mkProcess x p (\k => End)

