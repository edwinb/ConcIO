import IOu

data DoorState = Opened | Closed

data DoorH : DoorState -> Type where
     MkDH : DoorH s

data Result : (a : Type) -> (a -> Type) -> Type* where
     Res : {k : a -> Type} -> (val : a) -> k val -> Result a k

data DoorCmd : Type -> Type where
     Open : DoorH Closed -> DoorCmd (DoorH Opened)
     Knock : DoorH Closed -> DoorCmd ()
     Close : DoorH Opened -> DoorCmd (DoorH Closed)

data DoorLang : Type -> Type where
     Return : a -> DoorLang a
     Action : DoorCmd a -> DoorLang a
     (>>=) : DoorLang a -> (a -> DoorLang b) -> DoorLang b

testProg : DoorH Closed -> DoorLang ()
testProg h = do Action (Knock h)
                hbad <- Action (Open h)
                h <- Action (Close hbad)
                h <- Action (Close hbad)
                Return ()

