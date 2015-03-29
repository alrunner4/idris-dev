data MyShow : Type -> Type where
     ShowInstance : (show : a -> String) -> MyShow a

myshow : {auto inst : MyShow a} -> a -> String
myshow {inst = ShowInstance show} x1 = show x1 

%hint
showNat : MyShow Nat
showNat = ShowInstance show 

%hint
showFn : MyShow (a -> b)
showFn = ShowInstance (\x => "<< function >>")

%hint
showBools : MyShow (Bool, Bool)
showBools = ShowInstance (\x => "some bools")

%hint
showStuff : MyShow a -> MyShow b -> MyShow (a, b)
showStuff sa sb = ShowInstance showPair
  where
    showPair : (a, b) -> String
    showPair (x, y) = myshow x ++ ", " ++ myshow y

testShow : List (Bool, Bool) -> String
testShow [] = "" 
testShow (x :: xs) = myshow x ++ "\n" ++ testShow xs

testShow2 : List (Nat, Int -> Int) -> String
testShow2 [] = "" 
testShow2 (x :: xs) = myshow x ++ "\n" ++ testShow2 xs

main : IO ()
main = do putStrLn $ testShow2 [(2, (+1)), (3, abs)]
          putStrLn $ testShow [(True, False), (False, True)]



