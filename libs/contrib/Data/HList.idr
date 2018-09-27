module Data.HList
import Data.List

% default total
% access public export

namespace List {

  replaceElem : a -> ( xs : List a ) -> ( el : Elem x xs ) -> List a
  replaceElem x ( _ :: xs ) Here = x :: xs
  replaceElem x ( y :: xs )( There index ) = y :: replaceElem x xs index

}

infixr 7 ::

data HList : List Type -> Type where
	Nil : HList []
	(::) : x -> HList xs -> HList( x :: xs )

(++) : HList xs -> HList ys -> HList ( xs ++ ys )
(++) [] ys = ys
(++) ( x :: xs ) ys = x :: xs ++ ys

getElem : Elem x xs -> HList xs -> x
getElem Here ( x :: xs ) = x
getElem ( There p )( x :: xs ) = getElem p xs

replaceElem : ( el : Elem x xs ) -> HList xs -> r' -> HList( replaceElem r' xs el )
replaceElem Here ( x :: xs ) val = val :: xs
replaceElem( There p )( x :: xs ) val = x :: replaceElem p xs val

dropElem : ( el : Elem x xs ) -> HList xs -> HList( dropElem xs el )
dropElem Here ( x :: xs ) = xs
dropElem( There p )( x :: xs ) = x :: dropElem p xs

