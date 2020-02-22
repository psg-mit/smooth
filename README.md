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
