# smooth

## Docker instructions

On my machine, to set up the environment for Docker:
```
eval $(docker-machine env default)
```

#### Docker image:

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

For example, the paper (section 3.1) shows the computation of the the derivative of (ReLU(x))^2.
This can be reproduced by running `runDerivReluSquared`. It should compute immediately and return
the interval [0,0].
