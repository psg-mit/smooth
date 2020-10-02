FROM ubuntu:18.04

RUN apt-get update
RUN apt-get install -y \
        build-essential=12.4ubuntu1 \
        curl=7.58.0-2ubuntu3.10 \
        libmpfr-dev=4.0.1-1 \
        ghc=8.0.2-11 \
        vim

# install stack, unfortunately no versioning
RUN curl -sSL https://get.haskellstack.org/ | sh

ENV PATH="/usr/local/bin:${PATH}"

# add the repo to the container
RUN mkdir /source
COPY . /source
RUN cd source && stack setup
RUN cd source && stack build
