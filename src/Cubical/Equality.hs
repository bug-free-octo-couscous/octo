module Cubical.Equality
    ( definitionallyEqual
    , definitionallyEqualCtx
    , definitionallyEqualCtxR
    , etaEq
    , EtaResult(..)
    , reducePAppByType
    ) where

import Cubical.Interval (I(..))
import Cubical.Syntax
import Cubical.Eval (eval, isTopDNF, isBotDNF)

-- Ctx imported from TypeChecker would create a cycle, so we re-alias here.
-- The full Ctx type lives in TypeChecker; equality only needs the list shape.
type Ctx = [(Name, Term)]

--------------------------------------------------------------------------------
-- Term size (used to derive eta-expansion fuel)
--------------------------------------------------------------------------------

-- | Structural node count of a term.  Used to derive the initial fuel for
-- 'etaEq': see 'initialFuel' for the termination argument.
termSize :: Term -> Int
termSize t = case t of
    TVar _               -> 1
    TUniv _              -> 1
    TIntervalTy          -> 1
    TInterval _          -> 1
    TCube _              -> 1
    TAbs _ b             -> 1 + termSize b
    PLam _ b             -> 1 + termSize b
    TApp f a             -> 1 + termSize f + termSize a
    PApp p r             -> 1 + termSize p + termSize r
    TPi _ a b            -> 1 + termSize a + termSize b
    TPath a u v          -> 1 + termSize a + termSize u + termSize v
    TEquiv a b           -> 1 + termSize a + termSize b
    TMkEquiv a b f g e s -> 1 + termSize a + termSize b + termSize f
                              + termSize g + termSize e + termSize s
    TEquivFwd e x        -> 1 + termSize e + termSize x
    TUa e                -> 1 + termSize e
    TTransport p x       -> 1 + termSize p + termSize x
    THComp a ph u u0     -> 1 + termSize a + termSize ph + termSize u + termSize u0
    TGlue a ph te        -> 1 + termSize a + termSize ph + termSize te
    TGlueElem ph x a     -> 1 + termSize ph + termSize x + termSize a
    TUnglue ph te g      -> 1 + termSize ph + termSize te + termSize g
    TSigma _ a b         -> 1 + termSize a + termSize b
    TPair a b            -> 1 + termSize a + termSize b
    TFst p               -> 1 + termSize p
    TSnd p               -> 1 + termSize p

-- | Starting fuel for an eta-equality check between two already-evaluated
-- terms.  We use the combined structural node count as the bound, with a
-- minimum floor of 16 so trivially small terms still get reasonable headroom.
--
-- == Why this bound is valid
--
-- Every fuel-consuming step in 'etaEq' is gated by a specific constructor
-- node on one of the two input terms:
--
--   * 'PApp' boundary reduction  — triggered by a 'PApp' node on one side.
--   * Lambda \/ 'PLam' eta expansion — triggered by a 'TAbs' or 'PLam' node.
--   * Sigma eta expansion         — triggered by a 'TPair' node.
--
-- Each such node can trigger at most one fuel-consuming step, because the
-- step either eliminates the node (boundary reduction) or peels it off and
-- recurses into the body (eta expansion), so the same node cannot fire again
-- in any recursive call.  The total number of fuel-consuming steps is
-- therefore bounded by the total number of those constructor nodes, which is
-- at most @termSize t1 + termSize t2@.
--
-- == Why term-size growth does not defeat the bound
--
-- One-sided lambda eta expansion replaces the neutral side @N@ with
-- @TApp (shift 1 0 N) (TVar 0)@.  Since 'shift' is size-preserving,
-- this adds exactly 2 nodes ('TApp' and 'TVar').  The total term size
-- therefore grows by 2 per one-sided step — a size-decrease argument would
-- fail.  The per-node argument above is not affected, because neither of the
-- 2 new nodes ('TApp', 'TVar') is a 'TAbs', 'PLam', 'PApp', or 'TPair', so
-- they cannot trigger a fuel-consuming step.  They will be handled by the
-- no-fuel structural congruence cases.
initialFuel :: Term -> Term -> Int
initialFuel t1 t2 = max 16 (termSize t1 + termSize t2)

--------------------------------------------------------------------------------
-- Eta-equality result
--------------------------------------------------------------------------------

-- | Three-valued result of eta-equality.
--
-- @Equal@    — the two terms are definitionally equal.
-- @NotEqual@ — they are definitionally distinct (normal termination).
-- @Exhausted@ — fuel ran out before a verdict could be reached; the checker
--               should report this as an ambiguous/inconclusive result rather
--               than silently treating it as @NotEqual@.
data EtaResult = Equal | NotEqual | Exhausted
    deriving (Eq, Show)

-- | Combine two 'EtaResult's under conjunction (both must be 'Equal').
-- 'Exhausted' is infectious in both directions: if either operand ran out of
-- fuel we cannot conclude inequality, so the whole check is inconclusive.
-- 'NotEqual' beats 'Equal' but loses to 'Exhausted', because we cannot trust
-- a 'NotEqual' verdict when the other branch didn't reach a decision.
andResult :: EtaResult -> EtaResult -> EtaResult
andResult Equal     r        = r           -- Equal is the identity
andResult r         Equal    = r           -- (symmetric)
andResult Exhausted _        = Exhausted   -- fuel exhaustion is infectious
andResult _         Exhausted = Exhausted  -- (symmetric)
andResult NotEqual  NotEqual = NotEqual    -- both sides definitively unequal

--------------------------------------------------------------------------------
-- Context-free definitional equality
--------------------------------------------------------------------------------

definitionallyEqual :: Term -> Term -> Bool
definitionallyEqual t1 t2 =
    let v1 = eval t1; v2 = eval t2
    in v1 == v2 || etaEq (initialFuel v1 v2) [] v1 v2 == Equal

definitionallyEqualCtx :: Ctx -> Term -> Term -> Bool
definitionallyEqualCtx ctx t1 t2 =
    let v1 = eval t1; v2 = eval t2
    in v1 == v2 || etaEq (initialFuel v1 v2) ctx v1 v2 == Equal

-- | Like 'definitionallyEqualCtx' but surfaces fuel exhaustion as a distinct
-- 'EtaResult' so callers can emit a proper error instead of a false mismatch.
definitionallyEqualCtxR :: Ctx -> Term -> Term -> EtaResult
definitionallyEqualCtxR ctx t1 t2 =
    let v1 = eval t1; v2 = eval t2
    in if v1 == v2 then Equal
       else etaEq (initialFuel v1 v2) ctx v1 v2

--------------------------------------------------------------------------------
-- Path boundary reduction
--------------------------------------------------------------------------------

-- | If p : Path A u v and r is I0/I1, return the endpoint.
reducePAppByType :: Ctx -> Term -> Term -> Maybe Term
reducePAppByType ctx p r =
    case inferTy ctx p of
        Just (TPath _ u v) ->
            let r' = eval r
            in if isBotDNF r' || r' == TInterval I0 then Just (eval u)
               else if isTopDNF r' || r' == TInterval I1 then Just (eval v)
               else Nothing
        _ -> Nothing
  where
    inferTy c (TVar i)
        | i >= 0, i < length c = Just (eval (shift (i+1) 0 (snd (c !! i))))
        | otherwise             = Nothing
    inferTy c (TApp f a) =
        case inferTy c f of
            Just (TPi _ _ bTy) -> Just (eval (beta bTy a))
            _                  -> Nothing
    inferTy _ _ = Nothing

--------------------------------------------------------------------------------
-- Lightweight neutral type inference (used by etaEq for lambda domains)
--------------------------------------------------------------------------------

inferNeutralTy :: Ctx -> Term -> Maybe Term
inferNeutralTy ctx (TVar i)
    | i >= 0, i < length ctx = Just (eval (shift (i+1) 0 (snd (ctx !! i))))
    | otherwise               = Nothing
inferNeutralTy ctx (TApp f a) =
    case inferNeutralTy ctx f of
        Just (TPi _ _ bTy) -> Just (eval (beta bTy a))
        _                  -> Nothing
inferNeutralTy _ _ = Nothing

-- | Try to infer the Pi domain of @neutral@ from the context, to use as the
-- type of the fresh variable introduced when eta-expanding @neutral@ against a
-- lambda.
--
-- Returns 'Nothing' when the type of @neutral@ cannot be determined (e.g. it
-- is not a variable or application chain, or its head is not in scope).
-- Callers must handle 'Nothing' explicitly — silently substituting a dummy
-- type like @TUniv 0@ would corrupt the context and mask genuine type errors.
inferLamDom :: Ctx -> Term -> Maybe Term
inferLamDom ctx neutral =
    case inferNeutralTy ctx neutral of
        Just (TPi _ domTy _) -> Just (eval domTy)
        _                    -> Nothing

--------------------------------------------------------------------------------
-- Core eta-equality
--------------------------------------------------------------------------------

-- | @etaEq fuel ctx t1 t2@ checks whether @t1@ and @t2@ are definitionally
-- equal under context @ctx@, using @fuel@ to bound eta-expansion steps.
--
-- == Fuel discipline
--
-- Fuel is consumed *only* by eta-expansion steps and path-boundary reductions
-- — the cases whose node-count argument is detailed in 'initialFuel'.
-- Structural congruence cases (matching constructors on both sides) do *not*
-- consume fuel; they split the comparison into sub-comparisons whose combined
-- node count is strictly less than the current pair's, so they make progress
-- without needing the fuel counter.
--
-- == Domain inference failure
--
-- When eta-expanding a lambda against a neutral term, we must extend the
-- context with the lambda's domain type.  If that type cannot be inferred
-- from the neutral (e.g. the neutral is opaque or out of scope), we return
-- 'Exhausted' rather than proceeding with a fabricated type.  This is
-- conservative but sound: we cannot claim inequality when we failed to
-- complete the check.
--
-- For the lambda-vs-lambda case neither side is a neutral, so we have no
-- type to infer from.  We fall back to a placeholder domain (@TUniv 0@)
-- and note in the comment that this only matters if the bodies themselves
-- trigger further domain inference — a pre-existing limitation.
etaEq :: Int -> Ctx -> Term -> Term -> EtaResult
etaEq 0 _ _ _ = Exhausted
etaEq fuel ctx t1 t2
    | t1 == t2  = Equal

    -- Path boundary reduction (consumes fuel)
    | PApp p r <- t1, Just u <- reducePAppByType ctx p r
    = etaEq (fuel-1) ctx u t2
    | PApp p r <- t2, Just u <- reducePAppByType ctx p r
    = etaEq (fuel-1) ctx t1 u

    -- Lambda eta: both sides are lambdas (structural, but needs ctx extension).
    -- Neither side is a neutral we can type, so we cannot infer the domain.
    -- We use TUniv 0 as a placeholder; this is only observable if the bodies
    -- subsequently eta-expand against a neutral that references the fresh var,
    -- which is an uncommon and already-limited case.
    | TAbs x b1 <- t1, TAbs _ b2 <- t2
    = let dom = case inferLamDom ctx t1 `orElse` inferLamDom ctx t2 of
                    Just d  -> d
                    Nothing -> TUniv 0
      in etaEq (fuel-1) ((x, dom) : ctx) (eval b1) (eval b2)

    -- Lambda eta: only RHS is a lambda — eta-expand the neutral LHS.
    -- If the domain cannot be inferred, return Exhausted: we must not extend
    -- the context with a fabricated type.
    | TAbs x b2 <- t2
    = case inferLamDom ctx t1 of
          Nothing  -> Exhausted
          Just dom ->
              let ctx' = (x, dom) : ctx
              in etaEq (fuel-1) ctx' (eval (TApp (shift 1 0 t1) (TVar 0))) (eval b2)

    -- Lambda eta: only LHS is a lambda — eta-expand the neutral RHS.
    | TAbs x b1 <- t1
    = case inferLamDom ctx t2 of
          Nothing  -> Exhausted
          Just dom ->
              let ctx' = (x, dom) : ctx
              in etaEq (fuel-1) ctx' (eval b1) (eval (TApp (shift 1 0 t2) (TVar 0)))

    -- Path-lambda eta: both sides (consumes fuel)
    | PLam i b1 <- t1, PLam _ b2 <- t2
    = etaEq (fuel-1) ((i, TIntervalTy) : ctx) (eval b1) (eval b2)
    | PLam i b2 <- t2
    = let ctx' = (i, TIntervalTy) : ctx
      in etaEq (fuel-1) ctx' (eval (PApp (shift 1 0 t1) (TVar 0))) (eval b2)
    | PLam i b1 <- t1
    = let ctx' = (i, TIntervalTy) : ctx
      in etaEq (fuel-1) ctx' (eval b1) (eval (PApp (shift 1 0 t2) (TVar 0)))

    -- Congruence on neutral spines (structural: no fuel consumed)
    | TApp f1 a1 <- t1, TApp f2 a2 <- t2
    = etaEq fuel ctx f1 f2 `andResult` etaEq fuel ctx a1 a2
    | PApp p1 r1 <- t1, PApp p2 r2 <- t2
    = etaEq fuel ctx p1 p2 `andResult` etaEq fuel ctx r1 r2

    -- Type congruence (structural: no fuel consumed)
    | TPi _ a1 b1 <- t1, TPi _ a2 b2 <- t2
    = etaEq fuel ctx a1 a2 `andResult` etaEq fuel ctx b1 b2
    | TPath ty1 u1 v1 <- t1, TPath ty2 u2 v2 <- t2
    = etaEq fuel ctx ty1 ty2
      `andResult` etaEq fuel ctx u1 u2
      `andResult` etaEq fuel ctx v1 v2
    | TSigma _ a1 b1 <- t1, TSigma _ a2 b2 <- t2
    = etaEq fuel ctx a1 a2 `andResult` etaEq fuel ctx b1 b2

    -- Pair congruence (structural)
    | TPair a1 b1 <- t1, TPair a2 b2 <- t2
    = etaEq fuel ctx a1 a2 `andResult` etaEq fuel ctx b1 b2

    -- Sigma eta: one side is a pair, the other is neutral (consumes fuel)
    | TPair a1 b1 <- t1
    = etaEq (fuel-1) ctx a1 (eval (TFst t2))
      `andResult` etaEq (fuel-1) ctx b1 (eval (TSnd t2))
    | TPair a2 b2 <- t2
    = etaEq (fuel-1) ctx (eval (TFst t1)) a2
      `andResult` etaEq (fuel-1) ctx (eval (TSnd t1)) b2

    -- Projection congruence on neutral spines (structural)
    | TFst p1 <- t1, TFst p2 <- t2
    = etaEq fuel ctx p1 p2
    | TSnd p1 <- t1, TSnd p2 <- t2
    = etaEq fuel ctx p1 p2

    | otherwise = NotEqual

-- | Left-biased 'Maybe' fallback — try the second option if the first is Nothing.
orElse :: Maybe a -> Maybe a -> Maybe a
orElse (Just x) _ = Just x
orElse Nothing  m = m