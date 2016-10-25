{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds, FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}

{- SExp parser example from

Modular rollback through control logging: A pair of twin functional pearls
Olin Shivers and Aaron Turon
Proc. ICFP 2011
http://www.ccs.neu.edu/home/shivers/papers/modular-rollback.pdf
-}

module SExpParser where

import Eff1
import OpenUnion52

import System.IO
import Data.Char (isAlpha)


data SExp = A String | SExp :& SExp

infixr 5 :&
-- A "" means NIL

-- Use []
instance Show SExp where
  show (A "")  = "[]"
  show (A str) = show str
  show (x :& A "")  = "[" ++ show x ++ "]"
  show (x :& A str) = "[" ++ show x ++ " . " ++ show str ++ "]"
    -- why is this safe and sound
  show (x :& y)     = let '[':ys = show y in
    "[" ++ show x ++ " " ++ ys



-- EX: implement ``Failure is not an option''
abort = error "Abort"


-- Parser for S-expressions
-- Rather naive recursive-descent parser
-- (but similar to that indicated in Shivers and Turon's paper)

-- skip white space and return the next char
-- ZZZ inferred type? nowspace :: Member (Reader Char) r => Eff r Char
-- ZZZ why to ask? For uniformity
{-
nowspace = do
  c <- ask
  case c of
    '\n' -> nowspace
    ' '  -> nowspace
    c    -> return c
-}

-- XXX why _ in the constraint won't work here
sexp = nowspace >>= \case
  '(' -> open
  c   -> A <$> name c

-- Read and accumulate the name starting with a given character
-- ZZZ I like reading signatures. What is underscore
name  :: _ => Char -> Eff r String
name c | not (isAlpha c) = error "name"
name c = (c:) <$> name_other
 where
   name_other = do
         c <- ask
         -- UUU

-- EX: implement numbers

-- //
data PutBack v where
  PutBack :: Char -> PutBack ()
putback = send . PutBack


-- Saw the opening parenthesis. Begin to read a pair
open :: (Member PutBack r, Member (Reader Char) r) => Eff r SExp
open = nowspace >>= \case
  ')' -> return $ A ""
  c   -> putback c >> (:&) <$> sexp <*> cdr

-- Read the second component of a pair
cdr :: _ => Eff r SExp
cdr = nowspace >>= \case
  '.' -> sexp <* close
  c   -> putback c >> open

-- Assert a closing parenthesis
close :: _ => Eff r ()
close = nowspace >>= \case
  ')' -> return ()
  _   -> abort

-- The top-level parser
sexp_top :: _ => Eff r SExp
sexp_top = handlePutBack Nothing sexp


-- ZZZ How to implement putback?
-- Need to deal with two effects: handle PutBack and listen to Read
handlePutBack :: Member (Reader Char) r =>
                 Maybe Char -> Eff (PutBack ': r) w -> Eff r w
handlePutBack _ (Val x) = return x

{-
handlePutBack (Just c) (E u q) | Just Reader <- (prj' u)  =
  handlePutBack Nothing $ qApp q c
-- where prj' :: Member (Reader Char) r => Union r v -> Maybe (Reader Char v)
 where prj' :: Union r v -> Maybe (Reader Char v)
       prj' = prj
-}
handlePutBack bc (E u q) = case decomp u of
  Right (PutBack c) | bc == Nothing -> handlePutBack (Just c) $ qApp q ()
  Left  u      -> case prj' u of
    Just Reader | Just c <- bc -> handlePutBack Nothing $ qApp q c
    _                          -> E u (qComps q (handlePutBack bc))
 where prj' :: Member (Reader Char) r => Union r v -> Maybe (Reader Char v)
       prj' = prj

-- QUIZ: exhaustive pattern-match?

-- EX: use combinator library
-- EX: Effect to look ahead: peek

-- ------------------------------------------------------------------------
-- Editing disciplines

-- Do no editing, raw input
-- ZZZ signature is needed!
noEdit :: (MemberU2 Lift (Lift IO) r) => Eff (Reader Char ': r) w -> Eff r w
noEdit = handle_relay return $ \Reader k -> do
             c <- lift $ getChar
             lift $ putChar c
             k c


-- Handling backspace

data Checkpoint r w =
  Checkpoint Char           -- Char that was fed to the continuation
             (Checkpoints r w -> Arr r Char w)

type Checkpoints r w = [Checkpoint r w]

edit :: (MemberU2 Lift (Lift IO) r) =>
        Eff (Reader Char ': r) w -> Eff r w
edit = handle_relay_s [] (\_ x -> return x) $ \cks reader k -> do
  -- If we read a character before, it is now committed and accepted,
  -- echo it
  case cks of
    (Checkpoint c _):_  -> lift $ putChar c
    _                   -> return ()
  loop cks (case reader of Reader -> k)  -- ZZZ weird, eh?
 where
   loop cks k = do
     -- Ask for a new character
     c <- lift $ getChar
     case c of
       '\008' -> case cks of
                  []                 -> loop cks k
                  Checkpoint _ k:cks -> lift rubout >> loop cks k
       c   -> k (Checkpoint c k : cks) c

rubout :: IO ()
rubout = do
  putChar '\008'
  putChar ' '
  putChar '\008'

main :: IO ()
main = do
  hSetEcho stdin False
  hSetBuffering stdin NoBuffering
  hSetBuffering stdout NoBuffering
  -- QUIZ: What happens if we do just the following by mistake
  -- s <- runLift $ noEdit sexp
  s <- runLift $ edit sexp_top
  putChar '\n'
  print s

-- QUIZ: Why the last character is not eachoed