module Data.SubList
import Data.List

% default total
% access public export

data SubSet : { nil : s } -> { cons : e -> s -> s } -> { elem : e -> s -> Type } -> s -> s -> Type where

  Empty : SubSet {nil} {cons} {elem} nil b

  ConsSuper : SubSet {nil} {cons} {elem} a b -> SubSet {nil} {cons} {elem} a ( cons c b )

  ConsSub : { elem : t -> s -> Type }
    -> { c : t }
    -> ( e : elem x b )
    -> SubSet {nil} {cons} {elem} a b
    -> SubSet {nil} {cons} {elem} ( cons c a ) b

remainder : { a, b : s } -> SubSet {nil} {cons} a b -> s
remainder {nil} Empty = nil
remainder {cons} ( ConsSuper {c} a ) = cons c ( remainder a )
remainder( ConsSub _ b ) = remainder b

SubList : List a -> List a -> Type
SubList = SubSet { nil = Nil } { cons = (::) } { elem = Elem }

% hint
Full : SubList xs xs
Full{ xs =      Nil } = Empty
Full{ xs = x :: Nil } = ConsSub Here Empty
Full{ xs = x :: zs  } = ConsSub Here ( ConsSuper Full )

namespace Test {

  duplicate_reference : SubList [1,2,1] [3,2,1]
  duplicate_reference = ConsSub{ x = 1 } (There(There Here)) (
    ConsSuper( ConsSub{ x = 2 } Here (
      ConsSuper( ConsSub{ x = 1 } Here ( ConsSuper Empty ) )
    ) )
  )

  supers_first : SubList [1] [3,2,1]
  supers_first = let
    supers = ConsSuper( ConsSuper( ConsSuper Empty ) )
  in ConsSub{ x = 1 }( There( There Here ) ) supers

}
