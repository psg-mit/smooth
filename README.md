# smooth

Examples from the paper are located in the file `src/SmoothLang.hs`.
Each example is annotated with its approximate runtime.

For example, the paper (section 2) shows the computation of the the derivative of the `brightness` function which corresponds to the definition `runDerivBrightness` in `src/SmoothLang.hs`.

## Docker instructions

If necessary, set up the environment for Docker:
```
eval $(docker-machine env default)
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

To run examples from the paper, first navigate to `/src/` then you can view the examples file
with `vim SmoothLang.hs` and can run the examples with `stack ghci SmoothLang.hs`, which will
launch a repl with all of the examples loaded.

For example, the paper (section 1) shows the computation of the the derivative of the integral from 0 to 1 of the derivative of ReLU(x - c) at c=0.6.
This can be reproduced by running `runDerivIntegralRelu`. It should compute almost immediately and return
the interval [-0.4062500000000000000000, -0.3984375000000000000000].

Computations of type `Real` return a single interval which corresponds to the interval refined to
the precision specified with the `atPrec` function. On the other hand, computations of type
`DReal ()` produce and infinite stream of finer and finer results. This stream may be truncated
at any time with Ctrl+C.
