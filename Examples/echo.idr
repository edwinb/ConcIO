import Channels

echo : Protocol ['C, 'S] ()
echo = do msg <- 'C ==> 'S | String
          'S ==> 'C | Literal msg
          'S ==> 'C | Nat

echo_server : Server 'S 'C echo
echo_server chan
    = do (True @@ chan) <- listen chan
             | (False @@ chan) => echo_server chan
         (msg @@ chan) <- recv chan 
         chan <- send (MkLit msg) chan
         chan <- send (length msg) chan
         let chan = reset chan
         echo_server chan

echo_client : Client 'C 'S echo
echo_client s
    = do chan <- connect s
         print "Message: "
         msg <- getLine
         chan <- send msg chan
         (MkLit msg @@ chan) <- recv chan
         (len @@ chan) <- recv chan
         print ("ECHO: " ++ msg ++ " length " ++ show len ++ "\n")
         close chan

conc_main : Conc 'C ()
conc_main = do h <- start_server echo echo_server
               client_loop h 
  where client_loop h = do echo_client h
                           client_loop h


main : IO ()
main = exec conc_main

