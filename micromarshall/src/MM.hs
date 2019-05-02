module MM where

type Q = Rational

data R = R { approx :: Q -> Q }

q_to_R :: Q -> R
q_to_R q = R (\_ -> q)

rplus :: R -> R -> R
rplus (R x) (R y) = R (\eps -> x (eps / 2) + y (eps / 2))

rnegate :: R -> R
rnegate (R x) = R (\eps -> - x eps)

rminus :: R -> R -> R
rminus x y = rplus x (rnegate y)

rabs :: R -> R
rabs (R x) = R (\eps -> abs (x eps))

-- error = dy * (x + dx) + dx * y
rtimes :: R -> R -> R
rtimes (R x) (R y) = R (\eps ->
    let xmag = abs (x 1) + 1 in
    let ymag = abs (y 1) + 1 in
    let xeps = (eps / 2) / ymag in
    let yeps = (eps / 2) / (xmag + xeps) in
    x xeps * y yeps)

-- note: this is partial!
rsign :: R -> Bool
rsign (R x) = go 1 where
    go eps = if x eps - eps > 0 then True
        else if x eps + eps < 0 then False
        else go (eps / 2)

rsignum :: R -> R
rsignum x = q_to_R (if rsign x then 1 else -1)

instance Num R where
    (+) = rplus
    (*) = rtimes
    (-) = rminus
    abs = rabs
    negate = rnegate
    signum = rsignum
    fromInteger = q_to_R . fromInteger

-- partial comparison
rlt :: R -> R -> Bool
rlt (R x) (R y) = go 1 where
    go eps = if x eps + eps < y eps - eps then True
        else if y eps + eps < x eps - eps then False
        else go (eps / 2)

-- nondeterministic comparison with 0, error epsilon for false negatives
cmp_0_eps :: Q -> R -> Bool
cmp_0_eps eps (R x) = go 1 where
    go e = if x e - e > 0 then True
           else if x e + e < eps then False
           else go (e / 2)

-- Show that we indeed get nondeterminism with cmp_0_eps
one_with_low_approximations :: R
one_with_low_approximations = R (\eps -> 1 - eps / 2)

cmp_0_1_true :: Bool
cmp_0_1_true = cmp_0_eps 2 1

cmp_0_one_low_false :: Bool
cmp_0_one_low_false = cmp_0_eps 2 one_with_low_approximations