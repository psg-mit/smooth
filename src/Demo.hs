module Demo (
  module Demo,
  module SmoothLang,
  -- module FwdPSh,
  module Types.Real,
  VectorSpace,
  dmap,
  (:=>) (ArrD),
) where

import Prelude hiding ((^))
import SmoothLang
import FwdPSh
import FwdMode hiding (deriv)
import Types.Real

infixl 3 @>

(@>) :: CPoint FwdPSh.Real -> DReal () -> FwdPSh.Real
(@>) = atPrec

-- See paper:
-- https://dl.acm.org/doi/10.1145/3434284

-- Smooth as a language is basically the language of your calculus class.
--
-- We can evaluate any expression to arbitrary precision, but in order to do so,
-- we need to say what precision we want.
-- So basically, at the REPL, we always start out by saying our desired precision.
-- Here, we compute sqrt(2) to 2 decimals of precision.
it1 :: FwdPSh.Real
it1 = 1e-2 @> sqrt 2

-- Since we have arbitrary precision, here we'll evaluate that same expression
-- to 200 digits of precision, which is a lot more than the ~10 digits of precision
-- we'd get with floating point.
-- The lower and upper bounds of the interval that are returned have width at most 1e-200
-- and are guaranteed to contain the true answer.
it2 :: FwdPSh.Real
it2 = 1e-200 @> sqrt 2

-- How do you define square roots anyway?
-- The square root of 2 is the number y such that y^2 = 2.
-- And this gives us a method to compute it, too. We just need to search for the
-- right y that has that property.
-- Finding the value of a variable that satisfies an equality is root-finding,
-- and Newton's method is a popular and very efficient method for doing that.
-- It uses the derivative of the function in question.
-- Just like in your calculus class, every expression in sight is infinitely differentiable
-- so we can have a primitive `cut_root_with_bounds` that uses Newton's method, starting
-- with an interval [0, x] to search from and refine.
my_sqrt :: VectorSpace g => DReal g -> DReal g
my_sqrt x = cut_root_with_bounds 0 x (ArrD (\wk y -> dmap wk x - Types.Real.max 0 (y Types.Real.^ 2)))

-- And now we can get the same answer again, to 200 digits of precision!
-- So we can define square root in the language just from having the squaring function available.
it3 :: FwdPSh.Real
it3 = 1e-200 @> my_sqrt 2

-- As I said, everything in the language is infinitely differentiable.
-- You might remember that the derivative of f(x) = sqrt(x) is
-- f'(x) = 1 / (2 * sqrt(x)).
-- So f'(1) = 1/2. Let's confirm!
it4 :: FwdPSh.Real
it4 = 1e-2 @> deriv (ArrD (\_ -> my_sqrt)) 1

-- You might wonder: Newton's method uses the value and first derivative of a function
-- to get its root, but how do we get the derivative? The simple answer is that
-- we use the implicit function theorem.
-- Since the implicit function can itself be viewed as a smooth operation over its
-- arguments, it also tells us all the higher derivatives,
-- so we can get the second derivative of sqrt(x) at 1, too.
it5 :: FwdPSh.Real
it5 = 1e-200 @> deriv (ArrD (\_ -> deriv (ArrD (\_ -> my_sqrt)))) 1

-- If I remember from my calculus class, we have
-- f''(x) = -1 / 4 * x^(-3/2)
-- so f''(1) = -1 / 4
-- so this looks right!

my_integral :: VectorSpace g => DReal g -> DReal g -> (DReal :=> DReal) g -> DReal g
my_integral a b f = (b - a) * integral01 (ArrD (\wk x -> dmap wk f # (dmap wk a + (x - dmap wk a) / dmap wk (b - a))))

-- Integration is a smooth operation, and it was in our calculus class,
-- so that's a primitive that's available as well.
-- So here's a fancy way of defining the sine function:
my_sin :: VectorSpace g => DReal g -> DReal g
my_sin z = my_integral 0 z (ArrD (\_ x -> cos x))

-- Let's check that it looks good:
it6 :: FwdPSh.Real
it6 = 1e-2 @> my_sin (pi / 2)

-- Currently, the integration method is a simple Riemann-sum style
-- integration, but it would be possible to use higher-order methods that
-- use derivative information to compute results more quickly/efficiently.

-- We've all learned that the derivative of the integral of a function
-- gets you back to the same function. Let's check that the derivative of my_sin
-- is indeed cos.

it7 :: FwdPSh.Real
it7 = 1e-2 @> deriv (ArrD (\_ -> my_sin)) (pi / 2)

-- We all know that you can maximize a smooth function by taking its
-- derivative and finding the root where the derivative is 0. We've already
-- seen we can do root-finding, and we know we can take derivatives, so it shouldn't
-- be too surprising that we can find the argmax for functions.

-- Suppose I want to make an rectangular area as large as possible
-- with a total perimeter of 4.
-- Let x be the fraction of perimeter allocated to one side, so the other side is (p - x).
-- The area is 4 * x * (1 - x).
-- What's the maximum over x in [0, 1]?

it8 :: FwdPSh.Real
it8 = 1e-2 @> Types.Real.max01 (ArrD (\_ x -> 4 * x * (1 - x)))

-- And we can find the argmax, too:
it9 :: FwdPSh.Real
it9 = 1e-2 @> Types.Real.argmax01 (ArrD (\_ x -> 4 * x * (1 - x)))

