module Control.ST
import Control.IOExcept
import Data.HList
import Data.HVect
import Data.List
import Data.SubList
import Language.Reflection.Utils

% default total

infix 5 :::

public export
Resources : Type
Resources = List Type

public export
Resource : { rs : Resources } -> Type
Resource { rs } = ( r : Type ** Elem r rs )

public export % error_reverse
(:::) : { rs : Resources } -> ( r : Type ) -> { e : Elem r rs } -> Resource{rs}
(:::){ rs }{ e } r = ( r ** e )

public export
SubRes : List Type -> List Type -> Type
SubRes = SubList

% error_reduce
public export
assignResources : ( add : Resources ) -> ( remove : SubRes ys xs ) -> Resources
-- At the end, add the ones which were updated by the subctxt
assignResources{ xs = [] } new SubNil = new
-- `SubIn` is impossible with an empty `Resources` context.
assignResources{ xs = [] } new ( SubIn el _ ) = absurd el
-- Don't add the ones which were consumed by the subctxt
assignResources{ xs = z :: zs } [] ( SubIn el p ) = assignResources{ ys = dropElem xs el } [] p
-- Update to a new item corresponding at an existing `Resource`.
assignResources{xs}( n :: ns ) ( SubIn el p ) = n :: assignResources{ xs = dropElem xs el } ns p
-- This isn't the `Resource` you're looking for.
assignResources{ xs = x :: xs } new ( SubSkip p ) = x :: assignResources{xs} new p

--public export
--getVarType : (xs : Resources) -> VarInRes v xs -> Type
--getVarType ((MkRes v st) :: as) VarHere = st
--getVarType (b :: as) (VarThere x) = getVarType as x

--public export
--getCombineType : VarsIn ys xs -> List Type
--getCombineType VarsNil = []
--getCombineType (InResVar el y) = getVarType _ el :: getCombineType y
--getCombineType (SkipVar x) = getCombineType x

--public export
--dropCombined : VarsIn vs res -> Resources
--dropCombined {res = []} VarsNil = []
--dropCombined {res} (InResVar el y) = dropCombined y
--dropCombined {res = (y :: ys)} (SkipVar x) = y :: dropCombined x

--Composite : List Type -> Type
--Composite = HList

--public export
--combineVarsIn : ( res : Resources ) -> VarsIn ( comp :: vs ) res -> Resources
--combineVarsIn{ comp } res ( InResVar el x ) = ( ( comp ::: Composite( getCombineType x ) ) :: dropCombined ( InResVar el x ) )
--combineVarsIn( y :: ys )( SkipVar x ) = y :: combineVarsIn ys x

Env : Resources -> Type
Env = HList

envElem : Elem x xs -> Env xs -> Env[x]
envElem p xs = [ getElem p xs ]

--dropEntry : Env res -> (prf : VarInRes x res) -> Env (dropVarIn res prf)
--dropEntry (x :: env) VarHere = env
--dropEntry (x :: env) (VarThere y) = x :: dropEntry env y

--dropVarsIn : Env res -> (prf : VarsIn vs res) -> Env (dropCombined prf)
--dropVarsIn [] VarsNil = []
--dropVarsIn env (InResVar el z) = dropVarsIn (dropEntry env el) z
--dropVarsIn (x :: env) (SkipVar z) = x :: dropVarsIn env z

--getVarEntry : Env res -> (prf : VarInRes v res) -> getVarType res prf
--getVarEntry (x :: xs) VarHere = x
--getVarEntry (x :: env) (VarThere p) = getVarEntry env p

--mkComposite : Env res -> (prf : VarsIn vs res) -> Composite (getCombineType prf)
--mkComposite [] VarsNil = CompNil
--mkComposite env (InResVar el z) = getVarEntry env el :: mkComposite( dropEntry env el ) z
--mkComposite (x :: env) (SkipVar z) = mkComposite env z

--rebuildVarsIn : Env res -> (prf : VarsIn (comp :: vs) res) ->
--                Env (combineVarsIn res prf)
--rebuildVarsIn env (InResVar el p)
--     = mkComposite (dropEntry env el) p :: dropVarsIn env (InResVar el p)
--rebuildVarsIn (x :: env) (SkipVar p) = x :: rebuildVarsIn env p

{- Some things to make STrans interfaces look prettier -}

infix 6 :->

public export
data Action : Type -> Type where
  Stable : var -> Type -> Action ty
  Trans  : var -> Type -> ( ty -> Type ) -> Action ty
  Remove : var -> Type -> Action ty
  Add    : ( ty -> Resources ) -> Action ty

namespace Stable
  public export % error_reduce
  (:::) : var -> Type -> Action ty
  (:::) = Stable

namespace Trans
  public export
  data Trans ty = (:->) Type Type

  public export % error_reduce
  (:::) : var -> Trans ty -> Action ty
  (:::) lbl (st :-> st') = Trans lbl st (const st')

namespace DepTrans
  public export
  data DepTrans ty = (:->) Type (ty -> Type)

  public export % error_reduce
  (:::) : var -> DepTrans ty -> Action ty
  (:::) lbl (st :-> st') = Trans lbl st st'

public export
or : a -> a -> Either b c -> a
or x y = either( const x )( const y )

public export % error_reduce
add : Type -> Action Resource
add ty = Add(\ var => [ ST.(:::) var ty ] )

public export % error_reduce
remove : var -> Type -> Action ty
remove = Remove

% error_reduce
public export
addIfRight : Type -> Action( Either a Resource )
addIfRight ty = Add( either( const [] )(\ r => [ r ::: ty ] ) )

% error_reduce
public export
addIfJust : Type -> Action( Maybe Resource )
addIfJust ty = Add( maybe [] (\ var => [ var ::: ty ] ) )

export
data STrans : ( m : Type -> Type ) -> ( a : Type ) -> Resources -> ( a -> Resources ) -> Type where

  Pure : ( x : a ) -> STrans m a ( edge x ) edge

  (>>=) : STrans m a ctx edge1 -> ( ( x : a ) -> STrans m b ( edge1 x ) edge2 ) -> STrans m b ctx edge2

  Lift : Monad m => m t -> STrans m t ctx (\ _ => ctx )

  RunAs : Applicative m => STrans m t ctx1 (\ _ => ctx2 ) -> STrans m ( m t ) ctx1 (\ _ => ctx2 )

  New : s -> STrans m Resource ctx (\ r => ( r ::: s ) :: ctx )

  Delete : ( el : Elem r ctx ) -> STrans m () ctx (\ _ => dropElem ctx el )

  DropSubRes : { states : SubRes ys xs } -> STrans m ( Env ys ) xs (\ _ => remaindner states )

  --Split : ( el : Elem ( Composite vars ) ctx ) -> STrans m Resource ctx (\ vs => mkRes vs ++ updateRes res el ( State () ) )

  --Combine : ( comp : var ) -> ( vs : List var ) -> ( prf : VarsIn ( comp :: vs ) ctx ) -> STrans m () res (\ _ => ( combineVarsIn res prf ) )

  --ToEnd : ( el : Elem r rs ) -> STrans m () ctx (\ _ => ( drop ctx el ++ r ) )

  Call : STrans m t sub produces -> { consumes : SubRes sub old } -> STrans m t old (\ res => assignResources( produces res ) consumes )

  Read : { state : Elem r rs } -> STrans m r rs (\ _ => rs )
 
  Write : { state : Elem r rs } -> ( val : r' ) -> STrans m () rs (\ _ => ( replaceElem rs el r' ) )

namespace Loop
  export
  data STransLoop : ( m : Type -> Type ) -> ( a : Type ) -> Resources -> ( a -> Resources ) -> Type where
    (>>=) : STrans m a st1 st2_fn -> ( ( result : a ) -> Inf( STransLoop m b ( st2_fn result ) st3_fn ) ) -> STransLoop m b st1 st3_fn
    Pure : ( result : ty ) -> STransLoop m ty ( out_fn result ) out_fn

export
dropEnv : Env ys -> SubRes xs ys -> Env xs
dropEnv [] SubNil = []
dropEnv [] (InRes idx rest) = absurd idx
dropEnv (z :: zs) (InRes idx rest)
    = let [e] = envElem idx (z :: zs) in
          e :: dropEnv( dropElem idx ( z :: zs ) ) rest
dropEnv (z :: zs) (Skip p) = dropEnv zs p

keepEnv : Env ys -> (prf : SubRes xs ys) -> Env( remainder prf )
keepEnv env SubNil = env
keepEnv env( InRes el prf ) = keepEnv ( dropElem el env ) prf
keepEnv (z :: zs) (Skip prf) = z :: keepEnv zs prf

-- Corresponds pretty much exactly to 'updateWith'
rebuildEnv : Env new -> Env old -> ( consumes : SubRes sub old ) -> Env( assignResources new consumes )
rebuildEnv new [] SubNil = new
rebuildEnv new [] (InRes el p) = absurd el
rebuildEnv [] (x :: xs) (InRes el p) = rebuildEnv [] ( dropElem el ( x :: xs ) ) p
rebuildEnv( e :: es )( x :: xs )( InRes el p ) = e :: rebuildEnv es ( dropElem el (x :: xs) ) p
rebuildEnv new (x :: xs) (Skip p) = x :: rebuildEnv new xs p

runST : Env invars -> STrans m a invars outfn -> ( ( x : a ) -> Env( outfn x ) -> m b ) -> m b
runST env ( Pure       result    ) k = k result env
runST env ( (>>=)      prog next ) k = runST env prog (\ prog', env' => runST env' ( next prog' ) k )
runST env ( Lift       action    ) k = k <$> action <*> pure env
runST env ( RunAs      prog      ) k = runST env prog (\ res, env' => k ( pure res ) env' )
runST env ( New        val       ) k = k val ( val :: env )
runST env ( Delete     prf       ) k = k () ( dropElem prf env )
runST env ( DropSubRes{states}   ) k = k( dropEnv env prf )( keepEnv env prf )
--runST env ( Split      prf       ) k = let
--  val  = lookupEnv prf env
--  env' = updateEnv prf env ( Value () )
--in
--  k( mkVars val )( addToEnv val env' )
--  where
--    mkVars : Composite ts -> VarList ts
--    mkVars CompNil = []
--    mkVars( CompCons x xs ) = MkVar :: mkVars xs
--
--    addToEnv : ( comp : Composite ts ) -> Env xs -> Env ( mkRes( mkVars comp ) ++ xs )
--    addToEnv [] env = env
--    addToEnv( x xs ) env = x :: addToEnv xs env
--runST env (ToEnd var prf) k = k () (dropElem prf env ++ [lookupEnv prf env])
--runST env (Combine lbl vs prf) k = k () (rebuildVarsIn env prf)
runST env (Call prog {res_prf}) k =
  let env' = dropEnv env res_prf
  in runST env' prog (\ prog', envk => k prog' ( rebuildEnv envk env res_prf ) )
runST env (Read{state}) k = k (getElem state env) env
runST env (Write{state} val) k = k () (replaceElem state env val)

export
data Fuel = Empty | More( Lazy Fuel )

export partial
forever : Fuel
forever = More forever

runSTLoop : Fuel -> Env invars -> STransLoop m a invars outfn ->
            (k : (x : a) -> Env (outfn x) -> m b) ->
            (onDry : m b) -> m b
runSTLoop Dry _ _ _ onDry = onDry
runSTLoop (More x) env (prog >>= next) k onDry
    = runST env prog (\prog', env' => runSTLoop x env' (next prog') k onDry)
runSTLoop (More x) env (Pure result) k onDry = k result env

export
pure : (result : ty) -> STrans m ty (out_fn result) out_fn
pure = Pure

--export
--(>>=) : STrans m a st1 st2_fn -> ((result : a) -> STrans m b (st2_fn result) st3_fn) -> STrans m b st1 st3_fn
--(>>=) = Bind

export
lift : Monad m => m t -> STrans m t res ( const res )
lift = Lift

export
runAs : Applicative m => STrans m t in_res ( const out_res ) -> STrans m ( m t ) in_res ( const out_res )
runAs = RunAs

export
new : s -> STrans m Resource ctx (\ lbl => ( lbl ::: State s ) :: ctx )
new val = New val

export
delete : Elem( State st ) rs -> STrans m () res ( const( drop res prf ) )
delete lbl { prf } = Delete lbl prf

-- Keep only a subset of the current set of resources. Returns the
-- environment corresponding to the dropped portion.
export
dropSub : {auto prf : SubRes ys xs} ->
          STrans m (Env ys) xs (const (kept prf))
dropSub {prf} = DropSubRes prf

export
split : (lbl : var) ->
        {auto prf : InState lbl (Composite vars) res} ->
        STrans m (VarList vars) res
              (\vs => mkRes vs ++
                       updateRes res prf (State ()))
split lbl {prf} = Split lbl prf

--export
--combine : ( comp : var )
--  -> ( vs : List var )
--  -> { auto el : Elem ( State () ) ctx }
--  -> { auto var_prf : VarsIn ( comp :: vs ) ctx }
--  -> STrans m () ctx (\ _ => ( combineVarsIn res var_prf ) )
--combine comp vs {var_prf} = Combine comp vs var_prf

--export
--toEnd : (lbl : var) ->
--        {auto prf : InState lbl state res} ->
--        STrans m () res (const (drop res prf ++ [lbl ::: state]))
--toEnd lbl {prf} = ToEnd lbl prf

--export
--call : STrans m a ctx1 edge -> { auto res_prf : SubRes ctx1 ctx2 } -> STrans m a ctx2 (\ r => assignResources ( edge r ) ctx res_prf )
--call prog { res_prf } = Call prog res_prf

--export
--read : { auto prf : InState ( State ty ) res } -> STrans m ty res ( const res )
--read lbl { prf } = Read lbl prf

--export
--write : (lbl : var) ->
--        {auto prf : InState lbl ty res} ->
--        (val : ty') ->
--        STrans m () res (const (updateRes res prf (State ty')))
--write lbl {prf} val = Write lbl prf (Value val)

--export
--update : (lbl : var) ->
--         {auto prf : InState lbl (State ty) res} ->
--         (ty -> ty') ->
--         STrans m () res (const (updateRes res prf (State ty')))
--update lbl f = do x <- read lbl
--                  write lbl (f x)

namespace Loop
--   export
--   (>>=) : STrans m a st1 st2_fn ->
--          ((result : a) -> Inf (STransLoop m b (st2_fn result) st3_fn)) ->
--          STransLoop m b st1 st3_fn
--   (>>=) = Bind

   export
   pure : (result : ty) -> STransLoop m ty (out_fn result) out_fn
   pure = Pure

public export % error_reduce
out_res : ty -> List( Action ty ) -> Resources
out_res x [] = []
out_res x ( ( Stable lbl inr      ) :: xs ) = ( lbl ::: inr    ) :: out_res x xs
out_res x ( ( Trans  lbl inr outr ) :: xs ) = ( lbl ::: outr x ) :: out_res x xs
out_res x ( ( Remove lbl inr      ) :: xs ) =                       out_res x xs
out_res x (   Add            outr   :: xs ) =             outr x ++ out_res x xs

public export % error_reduce
in_res : List( Action ty ) -> Resources
in_res [] = []
in_res ( Stable lbl inr      :: actions ) = ( lbl ::: inr ) :: in_res actions
in_res ( Trans  lbl inr outr :: actions ) = ( lbl ::: inr ) :: in_res actions
in_res ( Remove lbl inr      :: actions ) = ( lbl ::: inr ) :: in_res actions
in_res ( Add            outr :: actions ) =                    in_res actions

public export % error_reduce
ST : (m : Type -> Type) ->
     (ty : Type) ->
     List (Action ty) -> Type
ST m ty xs = STrans m ty (in_res xs) (\result : ty => out_res result xs)

public export % error_reduce
STLoop : (m : Type -> Type) ->
         (ty : Type) ->
         List (Action ty) -> Type
STLoop m ty xs = STransLoop m ty (in_res xs) (\result : ty => out_res result xs)

-- Console IO is useful sufficiently often that let's have it here
public export
interface ConsoleIO( m : Type -> Type ) where
  putStr  : String -> STrans m   ()   xs (\ _ => xs )
  getStr  :           STrans m String xs (\ _ => xs )
  putChar : Char   -> STrans m   ()   xs (\ _ => xs )
  getChar :           STrans m  Char  xs (\ _ => xs )


export
putStrLn : ConsoleIO m => String -> STrans m () xs (const xs)
putStrLn str = putStr (str ++ "\n")

export
print : (ConsoleIO m, Show a) => a -> STrans m () xs (const xs)
print a = putStr $ show a

export
printLn : (ConsoleIO m, Show a) => a -> STrans m () xs (const xs)
printLn a = putStrLn $ show a

export
ConsoleIO IO where
  putStr  = lift . Interactive.putStr
  getStr  = lift   Interactive.getLine
  putChar = lift . Interactive.putChar
  getChar = lift   Interactive.getChar

export
ConsoleIO( IOExcept err ) where
  putStr  = lift . ioe_lift . Interactive.putStr
  getStr  = lift(  ioe_lift   Interactive.getLine )
  putChar = lift . ioe_lift . Interactive.putChar
  getChar = lift(  ioe_lift   Interactive.getChar )

export
run : Applicative m => ST m a [] -> m a
run prog = runST [] prog (\ res,env' => pure res )

export
runLoop : Applicative m => Fuel -> STLoop m a [] -> m a -> m a
runLoop fuel prog = runSTLoop fuel [] prog (\ res,env' => pure res )

||| runWith allows running an STrans program with an initial environment,
||| which must be consumed.
||| It's only allowed in the IO monad, because it's inherently unsafe, so
||| we don't want to be able to use it under a 'lift' in just *any* ST program -
||| if we have access to an 'Env' we can easily duplicate it - so it's the
||| responsibility of an implementation of an interface in IO which uses it
||| to ensure that it isn't duplicated.
export
runWith : Env res -> STrans IO a res resf -> IO( result ** Env( resf result ) )
runWith env prog = runST env prog (\ res,env' => pure( res ** env' ) )

export
runWithLoop : Env res -> Fuel -> STransLoop IO a res resf -> IO( Maybe( result ** Env( resf result ) ) )
runWithLoop env fuel prog = runSTLoop fuel env prog
  (\ res,env' => pure( Just( res ** env' ) ) )
  ( pure Nothing )

export
runPure : ST Basics.id a [] -> a
runPure prog = runST [] prog (\res, env' => res)

% language ErrorReflection

%error_handler
export
st_precondition : Err -> Maybe( List ErrorReportPart )
st_precondition( CantSolveGoal `( SubRes ~sub ~all ) _ ) = pure [
    TextPart "'call' is not valid here. ",
    TextPart "The operation has preconditions ",
    TermPart sub,
    TextPart " which is not a sub set of ",
    TermPart all
]
st_precondition( CantUnify _ tm1 tm2 _ _ _ ) = do
    reqPre  <- getPreconditions tm1
    gotPre  <- getPreconditions tm2
    reqPost <- getPostconditions tm1
    gotPost <- getPostconditions tm2
    pure (
        TextPart "Error in state transition:" ::
        renderPre  gotPre  reqPre ++
        renderPost gotPost reqPost
    )

  where
    getPreconditions : TT -> Maybe TT
    getPreconditions `( STrans     ~m ~ret ~pre ~post ) = Just pre
    getPreconditions `( STransLoop ~m ~ret ~pre ~post ) = Just pre
    getPreconditions _                                  = Nothing

    getPostconditions : TT -> Maybe TT
    getPostconditions `( STrans     ~m ~ret ~pre ~post ) = Just post
    getPostconditions `( STransLoop ~m ~ret ~pre ~post ) = Just post
    getPostconditions _                                  = Nothing

    renderPre : TT -> TT -> List( ErrorReportPart )
    renderPre got req = [
        SubReport [ TextPart "Operation has preconditions: ", TermPart req ],
        SubReport [ TextPart "States here are: ", TermPart got ]
    ]

    renderPost : TT -> TT -> List( ErrorReportPart )
    renderPost got req = [
        SubReport [ TextPart "Operation has postconditions: ", TermPart req ],
        SubReport [ TextPart "Required result states here are: ", TermPart got ]
    ]

st_precondition _ = Nothing
