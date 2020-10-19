# smooth

This is the artifact for the paper "λS: Computable semantics for differentiable programming with higher-order functions and datatypes".

This repository contains the implementation of <img src="https://render.githubusercontent.com/render/math?math=\lambda_S"> as an embedded language within Haskell.
We name this library _smooth_.

## List of claims

Our primary claim of this artifact is that it contains implementations of all of the code in the language presented in the paper.
Accordingly, our list of claims is a list of code examples from the paper and their corresponding implementation in this library.
All of the implementations for examples from the paper are located in the file `src/SmoothLang.hs`.
Each example is annotated in that file with its approximate runtime.
These runtimes came from running natively, rather than in a VM, so runtimes may be larger when running in a VM.
We now provide every code example in the paper.


### Section 1
Code in <img src="https://render.githubusercontent.com/render/math?math=\lambda_S">:
```
eps=1e-2> deriv (λ c ⇒ integral01 (λ x ⇒ relu (x - c))) 0.6
[-0.407, -0.398]
```

Implementation in _smooth_:
```haskell
-- Section 1: the integral from 0 to 1 of the derivative of ReLU(x - c) at c=0.6
derivIntegralRelu :: DReal ()
derivIntegralRelu =
  deriv (ArrD (\_ c -> (integral01 (ArrD (\wk x -> max 0 (x - (dmap wk c))))))) 0.6

-- Time: <1 second
-- Result: [-0.4062500000000000000000, -0.3984375000000000000000]
runDerivIntegralRelu :: Real
runDerivIntegralRelu = atPrec 1e-2 derivIntegralRelu
```
### Section 2
Code in <img src="https://render.githubusercontent.com/render/math?math=\lambda_S">:
Implementation of a raytracer from Figure 1
```
type Surface A = A → ℜ
firstRoot : (ℜ→ℜ) → ℜ ! language primitive
let dot (x y : ℜ^2) : ℜ = x[0] * y[0] + x[1] * y[1]
let scale (c : ℜ) (x : ℜ^2) : ℜ^2 = (c * x[0], c * x[1])
let norm2 (x : ℜ^2) : ℜ = x[0]^2 + x[1]^2
let normalize (x : ℜ^2) : ℜ^2 = scale (1 / sqrt (norm2 x)) x
deriv : (ℜ → ℜ) → (ℜ → ℜ) ! library function
let gradient (f : ℜ^2 → ℜ) (x : ℜ^2) : ℜ^2 =
    (deriv (λ z : ℜ ⇒ f (z, x[1])) x[0],
     deriv (λ z : ℜ ⇒ f (x[0], z)) x[1])
```
```
! camera assumed to be at the origin
let raytrace (s : Surface (ℜ^2)) (lightPos : ℜ^2) (rayDirection : ℜ^2) : ℜ =
    let t_star = firstRoot (λ t : ℜ ⇒ s (scale t rayDirection)) in
    let y = scale t_star rayDirection in let normal : ℜ^2 = - gradient s y in
    let lightToSurf = y - lightPos in
    max 0 (dot (normalize normal) (normalize lightToSurf))
    / (norm2 y * norm2 lightToSurf)
```
```
eps=1e-5> raytrace (circle (1, -3/4) 1) (1, 1) (1, 0)
[2.587289, 2.587299]
```
```
eps=1e-3> deriv (λ y : ℜ ⇒ raytrace (circle (0, y) 1) (1, 1) (1, 0)) (-3/4)
[1.3477, 1.3484]
```

Implementation in _smooth_:
```haskell
-- Section 2: raytracing
dot :: VectorSpace g => (DReal :* DReal) g -> (DReal :* DReal) g -> DReal g
dot (x0 :* x1) (y0 :* y1) = x0 * y0 + x1 * y1

scale :: VectorSpace g => DReal g -> (DReal :* DReal) g -> (DReal :* DReal) g
scale c (x0 :* x1) = (c * x0) :* (c * x1)

norm2 :: (DReal :* DReal) g -> DReal g
norm2 (x :* y) = x^2 + y^2

normalize :: VectorSpace g => (DReal :* DReal) g -> (DReal :* DReal) g
normalize x = scale (1 / sqrt (norm2 x)) x

gradient :: VectorSpace g => (DReal :* DReal :=> DReal) g -> (DReal :* DReal) g -> (DReal :* DReal) g
gradient f (x0 :* x1) =
  (deriv (ArrD $ \wk z -> dmap wk f # (z :* dmap wk x0)) x0) :* (deriv (ArrD $ \wk z -> dmap wk f # (dmap wk x1 :* z)) x0)

raytrace :: VectorSpace g => ((DReal :* DReal) :=> DReal) g ->
                             (DReal :* DReal) g ->
                             (DReal :* DReal) g -> DReal g
raytrace s lightPos u =
  let t = firstRoot (ArrD (\wk t -> dmap wk s # (scale t (dmap wk u)))) in
  let y = scale t u in
  let normal = gradient s y in
  let lightVector = lightPos `sub` y in
  max 0 (dot (normalize normal) (normalize lightVector))
  / (norm2 y * norm2 lightVector)
  where
  (x0 :* x1) `sub` (y0 :* y1) = (x0 - y0) :* (x1 - y1)

circle :: VectorSpace g => DReal g -> ((DReal :* DReal) :=> DReal) g
circle y0 = ArrD $ \wk (x :* y) -> ((x - 1)^2 + (y - dmap wk y0)^2) - 1

raytraceExample :: DReal ()
raytraceExample = raytrace (circle (-3/4)) (1 :* 1) (1 :* 0)

raytraceExampleDeriv :: DReal ()
raytraceExampleDeriv = deriv (ArrD (\_ y0 -> raytrace (circle y0) (1 :* 1) (1 :* 0))) (-3/4)

-- Time: 1 second
-- Result: [2.587289929104514485486379588564089986615867, 2.587298566457847103838396428782456969483227]
runRaytraceExample :: Real
runRaytraceExample = atPrec 1e-5 raytraceExample

-- Time: 12 seconds
-- Result: [1.347739015144645601713439374053190179150, 1.348337596821412823551715548182238961320]
runRaytraceExampleDeriv :: Real
runRaytraceExampleDeriv = atPrec 1e-3 raytraceExampleDeriv
```

#### Section 2.1
Code in <img src="https://render.githubusercontent.com/render/math?math=\lambda_S">:
```
let t_star y = firstRoot (λ t : ℜ ⇒ 1 - y^2 - (t - 1)^2)
```
```
deriv t_star y = - deriv (λ y0 : ℜ ⇒ f (t_star y) y0) y /
    deriv (λ t : ℜ ⇒ f t y) (t_star y)
```
```
deriv t_star y = - y / (t_star y - 1):
```
Implementation in _smooth_:
```haskell
-- Section 2.1
tStar :: VectorSpace g => DReal g -> DReal g
tStar y = firstRoot (ArrD (\wk t -> - (1 - dmap wk y^2 - (t - 1)^2)))

derivTStar :: VectorSpace g => DReal g -> DReal g
derivTStar y = deriv (ArrD (\_ -> tStar)) y

derivTStarAnalytic :: VectorSpace g => DReal g -> DReal g
derivTStarAnalytic y = - y / (tStar y - 1)

-- Time: <1 second
-- Result: [-1.133899683374569614339844628613941903, -1.133893143859001568699824674725477525]
runDerivTStar :: Real
runDerivTStar = atPrec 1e-5 (derivTStar (-3/4))

-- Time: <1 second
-- Result: [-1.133899683374569614339844628613941903, -1.133893143859001568699824674725477525]
runDerivTStarAnalytic :: Real
runDerivTStarAnalytic = atPrec 1e-5 (derivTStarAnalytic (-3/4))
```
#### Section 2.3
Code in <img src="https://render.githubusercontent.com/render/math?math=\lambda_S">:
```
eps=1e-1> deriv relu 0
(nontermination)
```
```
eps=2> deriv relu 0
[0.0, 1.0]
```
```
let brightness (y : ℜ) : ℜ =
    integral01 (λ y0 : ℜ⇒ max 0 ((y0 - y) / sqrt (1 + (y0 - y)2)))
```
```
eps=1e-3> deriv brightness (1/2)
[-0.4476, -0.4469]
```

Implementation in _smooth_:
```haskell
reluFirstDerivAt0 :: DReal ()
reluFirstDerivAt0 = deriv (ArrD (\_ x -> max 0 x)) 0

-- Time: <1 second
-- Result: [0.00000000000, 1.0000000000]
runReluFirstDerivAt0 :: Real
runReluFirstDerivAt0 = atPrec 2 reluFirstDerivAt0

-- Time: infinite (non-terminating)
-- Result: [0.00000000000, 1.0000000000]
runReluFirstDerivAt0nonterminating :: Real
runReluFirstDerivAt0nonterminating = atPrec 0.1 reluFirstDerivAt0

brightness :: VectorSpace g => DReal g -> DReal g
brightness y = integral01 (ArrD (\wk y0 -> max 0 ((y0 - dmap wk y) / sqrt (1 + (y0 - dmap wk y)^2))))

-- Time: ~4 seconds
-- Result: [-0.44750046730041503906250000000, -0.44692683219909667968750000000]
runDerivBrightness :: Real
runDerivBrightness = atPrec 1e-3 (deriv (ArrD (\_ -> brightness)) (1/2))
```

### Section 6
Code in <img src="https://render.githubusercontent.com/render/math?math=\lambda_S">:
```
> sqrt 2 : ℜ
[1.4142135619, 1.4142135624]
[1.414213562370, 1.414213562384]
[1.4142135623729, 1.4142135623733]
…
```
```
> (sqrt 2)^2
[1.9999999986, 2.0000000009]
[1.999999999985, 2.000000000058]
[1.9999999999991, 2.0000000000009]
…
```
```
> 2
[2.0000000000, 2.0000000000]
[2.000000000000, 2.000000000000]
[2.0000000000000, 2.0000000000000]
…
```
```
> (sqrt 2)^2 : ℜ
[1.9999999986, 2.0000000009]
[1.999999999985, 2.000000000058]
[1.9999999999991, 2.0000000000009]
…
```

Implementation in _smooth_:
```haskell
sqrt2 :: DReal ()
sqrt2 = sqrt 2

sqrt2Squared ::  DReal ()
sqrt2Squared = (sqrt 2)^2

two :: DReal ()
two = 2
```

#### Section 7
#### Section 7.1
Code in <img src="https://render.githubusercontent.com/render/math?math=\lambda_S">:

```
eps=1e-3> der mean uniform change
[0.0829, 0.0837]
```
```
eps=1e-2> der variance uniform change
[-0.005, 0.004]
```

Implementation in _smooth_:
```haskell
-- Section 7.1: derivative of the mean of a uniform distribution wrt. a line perturbation
change :: Integral DReal g
change = ArrD $ \_ f -> uniform # (ArrD (\wk x -> (x - 1/2) * dmap wk f # x))

derivMeanLinearChange ::  DReal ()
derivMeanLinearChange = let y :* dy = derivT mean (uniform :* change) in dy

-- Time: 2 seconds
-- Result: [0.082967042922973632812500000, 0.083699464797973632812500000]
runDerivMeanLinearChange :: Real
runDerivMeanLinearChange = atPrec 0.001 derivMeanLinearChange


-- Section 7.1: derivative of the variance of a uniform distribution wrt. a line perturbation
derivVarianceLinearChange ::  DReal ()
derivVarianceLinearChange = let y :* dy = derivT variance (uniform :* change) in dy

-- Time: 2 minutes
-- Result: [-0.004394948482513427734375, 0.004394948482513427734375]
runDerivVarianceLinearChange :: Real
runDerivVarianceLinearChange = atPrec 0.01 derivVarianceLinearChange

secondDerivVarianceLinearChange ::  DReal ()
secondDerivVarianceLinearChange =
  let ((y :* _) :* (_ :* dy2)) = derivT (ArrD (\_ -> derivT variance)) ((uniform :* change) :* (change :* (ArrD (\_ _ -> 0))))
  in dy2
```

#### Section 7.3
Code in <img src="https://render.githubusercontent.com/render/math?math=\lambda_S">:

```
eps=1e-3> hausdorffDist d_R2 l_shape (quarterCircle 0)
[0.4138, 0.4145]
```
```
eps=1e-1> deriv (λ y : ℜ ⇒ hausdorffDist d_R2 l_shape (quarterCircle y)) 0
[-0.752, -0.664]
```

Implementation in _smooth_:
```haskell
-- Section 7.3: Hausdorff distance between quarter-circle and L-shape.
quarter_circle :: VectorSpace g => DReal g -> Maximizer (DReal :* DReal) g
quarter_circle y0 = M.map (ArrD (\wk theta -> let y0' = dmap wk y0 in
  (cos (pi / 2 * theta)) :* (y0' + sin (pi / 2 * theta)))) M.unit_interval

quarter_square_perim :: VectorSpace g => Maximizer (DReal :* DReal) g
quarter_square_perim = M.union (M.map (ArrD (\_ x -> x :* 1)) M.unit_interval)
                               (M.map (ArrD (\_ y -> 1 :* y)) M.unit_interval)

hausdorffDistCircleL ::  DReal ()
hausdorffDistCircleL = hausdorffDist d_R2 quarter_square_perim (quarter_circle 0)

-- Time: 7 seconds
-- Result: [0.41384921849465670653300003702, 0.41440539111235744884709353399]
runHausdorffDistCircleL :: Real
runHausdorffDistCircleL = atPrec 0.001 hausdorffDistCircleL


-- Section 7.3: derivative of Hausdorff distance between quarter-circle and L-shape wrt. translation.
hausdorffDistTranslatedQuarterCircle :: DReal ()
hausdorffDistTranslatedQuarterCircle =
  deriv (ArrD (\_ y -> hausdorffDist d_R2 quarter_square_perim (quarter_circle y))) 0

-- Time: 52 seconds
-- Result: [-0.752, -0.664]
runHausdorffDistTranslatedQuarterCircle :: Real
runHausdorffDistTranslatedQuarterCircle = atPrec 0.1 hausdorffDistTranslatedQuarterCircle
```

These code examples use some libraries that are also described in the paper.
The library for integrals in Fig. 8 corresponds to the source file `src/Types/Integral.hs`.
The library for implicit surfaces in Fig. 9 corresponds to the source file `src/Types/OShape.hs`.
The library for generalized parametric surfaces in Fig. 10 corresponds to the source file `src/Types/KShape.hs`.


## Download, installation, and sanity testing
We provide both a virtual machine image that can be directly downloaded and run as well as a Dockerfile to load the dependencies in a docker image.

### Virtual machine image

We provide a virtual machine image with Ubuntu 20.04 with all of the dependencies preloaded, packaged together with this README file as SmoothVM.ova. You can import the .ova file into hypervisor software (e.g., virtualbox).
Note that the README file in the source code within that VM is out of date; please prefer using this README for evaluation.

Once the virtual machine is loaded, you can sign in to the user `lambda-s` with the password `lambda-s`. Open a terminal and use the command `cd smooth` to access the repository. View the examples from the paper with `vim src/SmoothLang.hs`.

To run the examples from the paper, run `stack repl` to launch the Haskell repl and run `:l SmoothLang` in the repl to load the library.

### Docker instructions

If necessary, set up the environment for Docker:
```
eval $(docker-machine env default)
```

In order to run all of the examples, it's necessary to allocate the docker image with at least 8GB of RAM. If you use Virtualbox (the default) for virtualization, you can set this with:
```
docker-machine stop
VBoxManage modifyvm default --memory 8192
docker-machine start
```

The Dockerfile is at the base of the source code directory. To build a docker image from the Dockerfile, run from the base of the source directory the command
```
docker build --tag=smooth .
```

To run the Docker image, run (from the base directory)
```
docker load < docker-image.tar.gz    #load docker image (if saved)
docker run -it smooth             #run docker image
```
The entire source directory is located at `/source/`.

### Sanity testing

To run examples from the paper, first navigate to `/src/` then you can view the examples file
with `vim SmoothLang.hs` and can run the examples with `stack ghci SmoothLang.hs`, which will
launch a repl with all of the examples loaded.
For instance, running `runDerivIntegralRelu` at the REPL should return the result `[-0.4062500000000000000000, -0.3984375000000000000000]` in less than 1 second.

## Evaluation Instructions

Our primary claim of this artifact is that it contains implementations of all of the code in the language presented in the paper. We provide every code example in the paper with the corresponding implementation in `src/SmoothLang.hs`.

There are two ways to run these code examples: interactively at the REPL, and as a compiled program that executes the programs that terminate with results in sequence.

To run code examples at the REPL, run `stack repl` to enter the Haskell REPL, then execute `:l SmoothLang` to load the SmoothLang file.
Then enter any expression within `src/SmoothLang.hs` at the command line.
For example, the paper (section 1) shows the computation of the the derivative of the integral from 0 to 1 of the derivative of ReLU(x - c) at c=0.6.
This can be reproduced by running `runDerivIntegralRelu`. It should compute almost immediately and return
the interval [-0.4062500000000000000000, -0.3984375000000000000000].
Note that `runHausdorffDistTranslatedQuarterCircle` may not work at the REPL due to excessive memory consumption (all the others should); however, it will work with the second method, as a compiled program.

To run all of the examples together as a compiled program, first build the project by running `stack build`, and then run `stack exec runexamples` to execute the compiled code (note that execution requires 8GB or more of RAM).

Computations of type `Real` return a single interval which corresponds to the interval refined to
the precision specified with the `atPrec` function. On the other hand, computations of type
`DReal ()` produce and infinite stream of finer and finer results. This stream may be truncated
at any time at the Haskell REPL with Ctrl+C.

Timing measurements for each computation shown in the paper are listed in `src/SmoothLang.hs`.
These are approximate measurements of the time taken using `stack repl` as shown above.
The compiled program `stack exec runexamples` takes roughly 1 minute to run all of the examples.

We note that the syntax for the code within the Haskell library is not identical to that shown in the paper.
A mechanical translation (using Template Haskell or a preprocessing stage) would be possible.
However, we did not implement any such translation.


## Additional artifact description

Here is a high-level overview of the types used in our implementation.
The category **CTop** in the paper corresponds to the type family `CMap` defined in `src/RealExpr.hs`.
The category **AD** in the paper corresponds to the type family `(:~>)` defined in `src/FwdMode.hs`.
Objects of the category **HAD** in the paper directly correspond to Haskell functors satisfying the typeclass `PShD`, defined in `src/FwdPSh.hs`.
The real type is the type family `DReal` defined in `src/Real.hs`.
Products are defined by the type family `:*` in `src/Experimental/PSh.hs`.
Exponentials are defined by the type family `:=>` in `src/FwdPSh.hs`.
Various derived types with **HAD** are defined in files in the directory `src/Types/`.