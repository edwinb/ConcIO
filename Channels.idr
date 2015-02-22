module Channels

import System.Concurrency.Raw
import Language.Reflection
import Language.Reflection.Errors
import System
import public Protocol
import IOu

data PID = MkPID Ptr

-- A channel connecting the source process (the local one) to a destination
-- process (the remote one)
data Channel : proc -> proc -> Actions -> UniqueType where
     MkChan : (t : PID) -> Channel src dest a

-- A replicable channel running as a server
data RChannel : proc -> Actions -> Type where
     MkRChan : (t : PID) -> RChannel dest a

-- Make a channel that connects to a server from a source process
-- TODO: Channels between src/dest are not distinguished other than by
-- the endpoints, so creating multiple channels will cause crashes.
-- In the RTS, need to create channel ids
rconnect : RChannel dest a -> Channel src dest a
rconnect (MkRChan t) = MkChan t 

-- Reset a recursive protocol back to its start state
reset : Channel s t (DoRec act) -> Channel s t act
reset (MkChan vm) = MkChan vm

--------- Language of communicating concurrent processes (+ basic IO)

-- (Type* means either a UniqueType or Type is accepted; we work under the
-- conservative assumption that any Type* is going to be unique.)

-- Dependent pair of possibly unique types (allows a computation to return
-- a value and an updated resource together, where the value explains what
-- the new resource state is)
infixl 5 @@

data Res : (a : Type*) -> (a -> Type*) -> Type* where
     (@@) : {k : a -> Type*} -> (val : a) -> k val -> Res a k

-- 'Listen' result: listening for a connection will either result in
-- no messages, so not ready to continue, or being ready to go on with
-- a protocol
listenRes : proc -> proc -> Actions -> Bool -> Type*
listenRes me t k True = Channel me t k
listenRes me t k False = Channel me t (DoListen t k)

dropElem : (xs : List a) -> Elem x xs -> List a
dropElem (x :: ys) Here = ys
dropElem (y :: ys) (There x) = dropElem ys x

-- Commands
data Cmd : proc -> List proc -> List proc -> Type* -> Type* where

     -- Send a value on a channel, return a new channel with the protocol
     -- moved on one step
     Send : (val : a) -> Channel me t (DoSend t a k) -> 
            Cmd me xs xs (Channel me t (k val))

     -- Receive a value from a channel, return value and a new channel with
     -- the protocol moved on one step
     Recv : (c : Channel me t (DoRecv t a k)) -> 
            Cmd me xs xs (Res a (\v => Channel me t (k v)))

     -- Check to see if there is anything in the process mailbox. If so,
     -- protocol can proceed.
     Listen : (c : Channel me t (DoListen t k)) ->
              {auto prf : Elem t xs} ->
              Cmd me xs xs (Res Bool (listenRes me t k))

     Connect : (c : RChannel t p) ->
               Cmd me xs (t :: xs) (Channel me t p)
     Close : (c : Channel me t End) -> 
             {auto prf : Elem t xs} -> Cmd me xs (dropElem xs prf) ()

     -- Some basic IO/system stuff (TODO: parameterise over possible effects)
     Print : String -> Cmd me xs xs ()
     GetLine : Cmd me xs xs String
     Pause : Int -> Cmd me xs xs ()

-- Coordination language; essentially an IO monad parameterised on
-- possibly unique things, also supporting 'fork' which forks a process
-- with a channel to run in sync with this one, and 'server' which starts
-- up a server listening for connections continuously

data CIO : proc -> List proc -> List proc -> Type* -> Type* where
     Return : {a : Type*} -> a -> CIO me xs xs a
     Action : {a : Type*} -> Cmd me xs xs' a -> CIO me xs xs' a
     Seq    : {a : Type*} -> Cmd me xs xs' a -> 
              (a -> Inf (CIO me xs' xs'' b)) -> CIO me xs xs'' b

     -- forked process must close the given channel, 
     -- meaning that the channel must be run to completion
     -- (assuming no other way to create a channel!)
     Fork   : {a : Type*} ->
              (proto : Protocol [c,s] ()) ->
              (Channel s c (protoAs s proto) -> CIO s (c :: xs) xs ()) ->
              (Channel c s (protoAs c proto) -> CIO c (s :: xs) xs' a) ->
              CIO c xs xs' a

     -- 'Void' in the server process means it can never return!
     -- An 'RChannel' can be passed around and converted to a Channel;
     -- this way we can use 'Fork' (with an empty protocol) to have
     -- multiple processes connecting to the server.
     RunServer : {a : Type*} ->
              (proto : Protocol [c,s] ()) ->
              (Channel s c (protoAs s (serverLoop c proto)) -> 
                   CIO s (c :: xs) (c :: xs) Void) ->
              (RChannel s (protoAs c proto) -> CIO c xs xs' a) ->
              CIO c xs xs' a

-- Wrap commands
%inline
send : (val : a) -> Channel me t (DoSend t a k) -> 
    CIO me xs xs (Channel me t (k val))
send v c = Action (Send v c)

%inline
recv : (c : Channel me t (DoRecv t a k)) -> 
    CIO me xs xs (Res a (\v => Channel me t (k v)))
recv c = Action $ Recv c

%inline
listen : (c : Channel me t (DoListen t k)) ->
      {auto prf : Elem t xs} ->
      CIO me xs xs (Res Bool (listenRes me t k))
listen c = Action $ Listen c

%inline
connect : (c : RChannel t p) ->
       CIO me xs (t :: xs) (Channel me t p)
connect c = Action $ Connect c

%inline
close : (c : Channel me t End) -> 
     {auto prf : Elem t xs} -> CIO me xs (dropElem xs prf) ()
close c = Action $ Close c

%inline
print : String -> CIO me xs xs ()
print s = Action $ Print s

%inline
getLine : CIO me xs xs String
getLine = Seq GetLine (\x => Return (trim x))

%inline
pause : Int -> CIO me xs xs ()
pause x = Action $ Pause x

-- More convenient ways to fork process/start server

fork : (proto : Protocol [c,s] ()) ->
       (Channel s c (protoAs s proto) -> CIO s (c :: xs) xs ()) ->
       CIO c xs (s :: xs) (Channel c s (protoAs c proto))
fork p proc = Fork p proc (\c => Return c)

start_server : (proto : Protocol [c,s] ()) ->
         (Channel s c (protoAs s (serverLoop c proto)) -> 
              CIO s (c :: xs) (c :: xs) Void) ->
         CIO c xs xs (RChannel s (protoAs c proto))
start_server p proc = RunServer p proc (\c => Return c)

--------- Give it 'do' notation (%inline helps get past totality checker)

%inline
%no_implicit
(>>=) : CIO me xs xs' a -> (a -> CIO me xs' xs'' b) -> CIO me xs xs'' b
(>>=) (Return x) k = k x 
(>>=) (Action x) k = Seq x (\x' => k x')
(>>=) (Seq y f) k = Seq y (\y' => with Main do ky' <- f y'
                                               k ky')
(>>=) (Fork p proca procb) k 
   = Fork p proca (\pid => with Main do pb <- procb pid
                                        k pb)
(>>=) (RunServer p proca procb) k 
   = RunServer p proca (\pid => with Main do pb <- procb pid
                                             k pb)


-------- Error handler for displaying Channel errors clearly

%language ErrorReflection

chanPart : TT -> Maybe (List ErrorReportPart)
chanPart `(DoSend {proc=~p} ~dest ~v ~rest) 
  = Just [TextPart "Send to", TermPart dest]
chanPart `(DoRecv {proc=~p} ~src ~v ~rest)
  = Just [TextPart "Recv from", TermPart src]
chanPart `(DoListen {proc=~p} ~client ~rest)
  = Just [TextPart "Listen to", TermPart client]
chanPart `(DoRec ~act)
  = Just [TextPart "Rec", TermPart act]
chanPart `(End) = Just [TextPart "End of channel"]
chanPart (App (Bind _ _ f) _) = chanPart f
chanPart t = Just [TermPart t]
chanPart _ = Just [TextPart "unknown action"]

chanError : TT -> TT -> Maybe (List ErrorReportPart)
chanError x y = return $ 
                    [TextPart "Channel Error: "]
                     ++ !(chanPart y) ++
                    [TextPart "used when"]
                     ++ !(chanPart x) ++
                    [TextPart "required"]

%error_handler
channel_err : Err -> Maybe (List ErrorReportPart)
channel_err (CantUnify _ `(Channel {proc=~proc} ~m ~t ~s) 
                         `(Channel {proc=~proc'} ~m' ~t' ~s') _ _ _)
     = chanError s s'
channel_err (CantUnify _ _ _ e@(CantUnify _ _ _ _ _ _) _ _) = channel_err e
channel_err (CantUnify _ m m' _ _ _) = chanError m m'
channel_err _ = Nothing 

-------- Evaluator for the command language

execCmd : Cmd me xs xs' a -> IOu a
execCmd (Print x) = MkIOu (putStr x)
execCmd GetLine = MkIOu getLine
execCmd (Pause i) = MkIOu (usleep i)

execCmd (Listen (MkChan (MkPID pid)))
        = do m <- MkIOu listenMsgs
             case m of
                  Nothing => pure (False @@ (MkChan (MkPID pid)))
                  Just newpid => pure (True @@ (MkChan (MkPID newpid)))
execCmd (Send val (MkChan (MkPID pid))) 
        = do MkIOu (sendToThread pid val)
             pure (MkChan (MkPID pid))
execCmd (Recv (MkChan (MkPID pid)))
        = do v <- MkIOu (getMsgFrom pid)
             pure (v @@ (MkChan (MkPID pid)))
execCmd (Connect r) = pure (rconnect r)
execCmd (Close _) = pure ()

execu : CIO me xs xs' a -> IOu a
execu (Return x) = pure x 
execu (Action x) = execCmd x
execu (Seq x f) = do x' <- execCmd x; execu (f x')
execu (Fork _ sp cp) 
    = do pid <- MkIOu (fork (do run (execu (do sp (MkChan (MkPID prim__vm))
                                               Return ()))))
         execu (cp (MkChan (MkPID pid)))
execu (RunServer _ sp cp)
    = do pid <- MkIOu (fork (do run (execu (sp (MkChan (MkPID prim__vm))))
                                return ()))
         execu (cp (MkRChan (MkPID pid)))

exec : CIO me [] [] a -> IO a
exec p = run (execu p)

---------- Various types of program

-- Top level of a concurrent system
Conc : Type -> Type -> Type
Conc p r = {xs : _} -> CIO p xs xs r

-- Type of a server process running a protocol
Server : (s, c : proc) -> Protocol [c, s] () -> Type*
Server s c p = {xs : _} ->
               Channel s c (protoAs s (serverLoop c p)) ->
               CIO s (c :: xs) (c :: xs) Void

-- Type of a client process running a protocol
Client : (c, s : proc) -> Protocol [c, s] () -> Type*
Client c s p = {xs : _} ->
               RChannel s (protoAs c p) ->
               CIO c xs xs ()

data Literal : String -> Type where
     MkLit : (x : String) -> Literal x

