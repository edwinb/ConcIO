import IOu

data DoorState = Opened | Closed

data DoorH : DoorState -> UniqueType where
     MkDH : DoorH s

infix 5 @@

data Res : (a : Type*) -> (a -> Type*) -> Type* where
     (@@) : {k : a -> Type*} -> (val : a) -> k val -> Res a k

data DoorCmd : Type* -> Type* where
     Open : DoorH Closed -> 
            DoorCmd (Res Bool (\ok => if ok then DoorH Opened
                                            else DoorH Closed))
     Knock : DoorH Closed -> DoorCmd (DoorH Closed)
     Close : DoorH Opened -> DoorCmd (DoorH Closed)

data DoorLang : Type* -> Type* where
     Return : {a : Type*} -> a -> DoorLang a
     Action : DoorCmd a -> DoorLang a
     (>>=) : DoorLang a -> (a -> DoorLang b) -> DoorLang b

testProg : DoorH Closed -> DoorLang (DoorH Closed)
testProg h = do h <- Action (Knock h)
                (True @@ h) <- Action (Open h) | (False @@ h) => Return h
                Action (Close h)

