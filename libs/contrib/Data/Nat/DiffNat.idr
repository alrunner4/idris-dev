module Data.Nat.DiffNat

data DiffNat : Nat -> Nat -> Type where
	DiffLT : diff + low = high -> DiffNat low high
	DiffGT : diff + low = high -> DiffNat high low
	DiffEq : low = high -> DiffNat low high

diff : ( n : Nat ) -> ( m : Nat ) -> DiffNat n m

diff Z Z = DiffEq Refl

diff Z ( S k ) = DiffLT ( plusZeroRightNeutral ( S k ) ) { diff = S k }
diff ( S k ) Z = DiffGT ( plusZeroRightNeutral ( S k ) ) { diff = S k }

diff ( S x ) ( S y ) with ( diff x y )

	-- x = y -> S x = S y
	| DiffEq xEQy = DiffEq ( eqSucc x y xEQy )

	 -- diff + x = y -> diff + S x = S y
	| DiffLT xLTy { diff } = DiffLT SxLTSy { diff } where
		SxLTSy = rewrite ( sym $ plusSuccRightSucc diff x ) in rewrite xLTy in Refl

	 -- diff + y = x -> diff + S y = S x
	| DiffGT xGTy { diff } = DiffGT SxGTSy { diff } where
		SxGTSy = rewrite ( sym $ plusSuccRightSucc diff y ) in rewrite xGTy in Refl
