module NLFitting
  ( fitSystemThrow1
  , fitSystemThrow
  , fitSystem
  )
  where

import Data.Foldable
import Data.Reflection (Reifies)
import qualified Numeric.LinearAlgebra as LA
import qualified Control.Monad.State.Strict as S
import qualified Numeric.AD.Mode.Reverse as R
import qualified Numeric.AD.Internal.Reverse as R
import Text.Printf
import Data.MemoUgly
import Data.Bifunctor
import Numeric.GSL.Fitting

import qualified Symbolic.Matrix as S
import Solving
import Symbolic
import Bump
import Number
import Traversables
import Percent

--fitTest :: [(Double, [Double])]
fitTest :: N a => (Maybe a, [[Double]]) -- [[(String, Double)]])
fitTest = d2xda2Bump `seq` (Just d2xda2Bump,
--            R.jacobian system is
  R.jacobian (\ [a,b] ->
    map (unlift . flip diff "a") (system [tag "a" (lift a), tag "b" (lift b)]))
    is
--   [[toD $ diff (diff x "a") i | i <- ["a", "b"]]
--   |x <- system [tag "a" a, tag "b" b] :: [Expr Double]
--   ]
--   [[("da2", bumpDiff2 (\ x -> system [a+x,b] !! o) 0 h)
--    ,("dadb", bumpDiffMixed (\ x y -> system [a+x,b+y] !! o) 0 0 h)
--    ,("db2", bumpDiff2 (\ x -> system [a,b+x] !! o) 0 h)]
--   | o <- [0,1]]
                           )

  where
    h = 0.000001
--    d2xda2Bump = bumpDiffMixed (\ x y -> system [a+x,b+y] !! 1) 0 0 0.000001
    d2xda2Bump = bumpDiff2 (\ x -> system [a,b+x] !! 0) 0 0.00001
    a,b :: N a => a
    a = 0.2
    b = 0.2
    is :: N a => [a]
    is = [a, b]
    system :: N a => [a] -> [a]
    system inputs =
      (\ [a,b] -> fitSystemThrow [a,b] [0.5,0.5] $ \ [a,b] [x,y] ->
      [  sin (exp a)^3 + sin b - x^2 - 1
      ,  2*y^3 - x
      ]) inputs
--     d2xda2Bump = bumpDiff (\ x -> head $ system [a+x,b,c]) 0 0.0001
--     is@[a,b,c] = [1,1,1]
--     system inputs =
--       (\ [a,b,c] -> fitSystemThrow [a,b,c] [0.5, 0.5, 0.5] $ \ [a,b,c] [x,y,z] ->
--       [  x^2 + b*y^3 - 9
--       ,a*x^2 -   y      - c
--       ,  y - x - z^2
--       ]) inputs
--       попробовать с "системой" из одного уравнения x^2 - 4
--       первая производная 2x = 4
--       вторая производная 2

-- | Replace elements of 'Traversable'
-- @replace t (toList t) = t@
replace :: Traversable t => [a] -> t b -> t a
replace l t = S.evalState (mapM (const $ S.state (\ (x:xs) -> (x,xs))) t) l

{-# INLINE fitSystemThrow1 #-}
fitSystemThrow1
  :: (Traversable i, N a)
  => i a -- ^ n inputs
  -> a -- ^ guess
  -> (forall a . N a => i a -> a -> a)
     -- ^ n inputs -> guess -> (result, error)
  -> a -- ^ result with derivatives to inputs
fitSystemThrow1 i g f =
  unT1 $ fitSystemThrow i (T1 g) (\ i (T1 g) -> [f i g])

{-# INLINE fitSystemThrow #-}
fitSystemThrow
  :: (Traversable i, Traversable o, N a, Show a)
  => i a -- ^ n inputs
  -> o a -- ^ m guesses
  -> (forall a . N a => i a -> o a -> [a])
     -- ^ n inputs -> m guesses -> (result, m errors)
  -> o a -- ^ results with derivatives to inputs
fitSystemThrow i o f =
  either error (\ o' -> replace o' o)
  $ fitSystem (toList i) (toList o)
  $ \ ni no -> f (replace ni i) (replace no o)

-- | Solve a system of non-linear equations for a set of inputs.
--
-- Uses Levenberg-Marquardt fitting from GSL with jacobians computed
-- using AD.
--
-- Results have derivatives to inputs computed via the implicit
-- function theorem.
--
-- Can be used to plug a model parameters calibration
-- (m parameters -> m equations = 0) into an AD framework.
fitSystem
  :: N a
  => [a] -- ^ n inputs
  -> [a] -- ^ m guesses
  -> (forall a . N a => [a] -> [a] -> [a])
     -- ^ n inputs -> m guesses -> m errors
  -> Either String [a] -- ^ results with derivatives to inputs
fitSystem inputs guesses system0
  | err > 1e-10 = -- Sum of squared residuals (sum . map (^2))
    -- if there's a big error, there's a big chance that
    --  * LA.inv will fail with a singular matrix
    --  * LA.inv will not fail, but derivatives will be incorrect
    --    (either completely missing out some of the dependencies,
    --    or be off)
    Left $ printf
      ("Didn't converge after %.0f iterations:\n" <>
      "  error           %10.3g\n" <>
      "%s" <>
      "  inputs          %s\n" <>
      "  initial guesses %s\n" <>
      "  last guesses    %s\n" <>
      "  difference      %s")
    nIterations err
    (unlines $
     zipWith (\ i e -> printf "    %2d %10.7f%%" (i::Int) (e*100))
       [0..] $ map fst $ jrMemo lastGuesses)
    (showDL inputsD) (showDL guessesD) (showDL lastGuesses)
    (unwords $ map fmtP $ zipWith pct lastGuesses guessesD)
  | otherwise =
--   trace (show path) $
--   map realToFrac results
--  trace (printf "%s %d x %d" (exprType proxy) m n) $
  Right $
    case dLevel proxy of
      DLNone -> map toN results
      DL1st  -> resultsWith1stDerivatives
      DLAny  -> resultsWith2ndDerivatives
--       trace (show (jr results, "inv", LA.inv (jr results), guesses, inputsD, results, ji inputsD, LA.dispf 3 jResultsInputs)) $
  where
    (proxy:_) = toList inputs
    (nIterations:err:lastGuesses) = LA.toList $ last $ LA.toRows path
    -- numerically computed 1st order derivatives,
    -- fast, but AD won't work if the result is symbolically differentiated
    -- (as there are no 2nd-order derivatives)
    resultsWith1stDerivatives =
      zipWith (\ r dis ->
        explicitD
          inputs
          (map (first toN) $ filter ((/= 0) . fst) $ zip (LA.toList dis) [0..])
          [] -- no hessian
          (toN r))
      results
      (LA.toRows jResultsInputs)
    -- mixed symbolic-AD computed 2nd-order derivatives
    -- very slow, but 'diff' of the result produces correct AD derivatives
    resultsWith2ndDerivatives =
      [explicitD
       inputs
       -- 1st order
       [(toN d, ii) | ii <- [0..n-1], let (d,_) = j S.!. (io,ii), d /= 0]
       -- 2nd order
       [-- trace (printf "∂²o%d/∂i%d∂i%d = %f" io ix iy d) $
        (toN (if ix == iy then d/2 else d), ix, iy)
       |ix <- [0..n-1]
       ,iy <- [ix..n-1]
       ,let (_dodx, splitAt n -> (dis,dos)) = j S.!. (io,ix)
       ,let d = sum $ [dis !! iy] <> [dos !! v * fst (j S.!. (v,iy)) | v <- [0..m-1]]
       ,d /= 0]
       -- result
       (toN r)
      |(io, r) <- zip [0..] results]

    -- Jacobian of results to inputs via the implicit function theorem
    -- https://en.wikipedia.org/wiki/Implicit_function_theorem#Statement_of_the_theorem
    jResultsInputs = (- (LA.inv $ jr results)) <> ji inputsD
    jr = matrix m m . map snd . jrMemo
    ji = matrix m n . R.jacobian (\ i -> system i (map toN results))

    jrMemo :: [Double] -> [(Double, [Double])]
    jrMemo = memo $ R.jacobian' (\ r -> system (map toN inputsD) r)

    -- Same as above but also contains second order derivatives
    -- m x n = (∂o_𝑜/∂i_𝑖, (∂(∂o_𝑜/∂i_𝑖)/∂i_[1..n], ∂(∂o_𝑜/∂i_𝑖)/∂o_[1..m]))
--    j :: S.M (Double, (Array Int Double, Array Int Double))
    j = R.jacobian' ift (inputsD <> results)
--    splitdido (dodi, splitAt n -> (dis,dos)) = (dodi, (dis,dos))
--      (dodi, (listArray (0,n-1) dis, listArray (0,m-1) dos))
    ift
      :: Reifies s R.Tape
      => [R.Reverse s Double] -> S.M (R.Reverse s Double)
    ift adInputs = -- ~60% of the time, mostly diff
                   -- 40% partials (from 'j')
      let (is, rs) = splitAt n adInputs
          x = tagged "i" is
          y = tagged "g" rs
          f = system x y
          -- symbolic jacobian, immediately converted back to AD
          fJ xs = unlift <$> S.jacobian f xs
      in
--        trace (show (map (length . showExprWithSharing) f, show . showExprWithSharing <$> S.jacobian f y)) $
        -- compute jResultsInputs on AD values
        S.matnegate (S.invert $ fJ y) `S.matmul` fJ x

    (LA.toList -> results, path) =
      nlFitting LevenbergMarquardtScaled
      1e-10 -- error
      1e-10 -- per-iteration change in the error to stop if the
            -- fitting error can no longer be improved
      100 -- max iterations
      (LA.fromList . map fst . jrMemo . LA.toList)
      (jr . LA.toList)
      (LA.fromList guessesD)
    inputsD = map toD inputs
    guessesD = map toD guesses
    m = length guesses
    n = length inputs
    system is gs
      | length es /= m = error $ "system returned " <> show (length es)
        <> " equations instead of " <> show m
      | otherwise = es
      where es = system0 (replace is inputs) (replace gs guesses)
    fmtP (Percent p)
      | abs p < 5 && abs p > 0.0001 = printf "%9.5f%%" p
      | otherwise = printf "%10.3e" (p/100)
    fmtD = printf "%10.3g" -- 1.123e-197 is 10 characters
    showDL = unwords . map fmtD
    matrix m n = (LA.><) m n . concat -- == LA.fromLists
    tagged prefix is =
      zipWith (\ n v -> tag (prefix <> show n) $ lift v) [0..] is

test = (x :: Double, dgda `pct` dgdaBump, dgdb `pct` dgdbBump
       , dgda `pct` fdgda, dgdb `pct` fdgdb
       , d2gda2Bump
       )
  where
    [fdgda, fdgdb] = R.grad (\ as -> fitSystemThrow1 as 0.5 f) [ia,ib]
    dgda = - (1/dx) * dfda
    dgdb = - (1/dx) * dfdb
    d2gda2Bump = bumpDiff (\ a -> bumpDiff (\ a -> nx a ib) a 0.00001) ia 0.00001
    dgdaBump = bumpDiff (\ a -> nx a ib) ia 0.00001
    dgdbBump = bumpDiff (\ b -> nx ia b) ib 0.00001
    Right (x, [dfda, dfdb], dx) = n ia ib
--    _ :< [_ :< d2fda2,d2fdb2]:_) = AD.grads (\ (x:is) -> f is x) [x,ia,ib]
    ia = 1
    ib = 2
    n a b = newton (\ as x -> f as x) [a, b] 0.5
    nx a b = let Right (x,_,_) = n a b in x
    f [a,b] x = a * cos x - b * x^3
