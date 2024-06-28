FROM ubuntu:22.04

RUN apt-get update && apt-get install -y software-properties-common && \
    apt-get install -y build-essential aspcud unzip curl git m4 \
        opam bubblewrap

WORKDIR /opt

RUN apt-get update && \
    apt-get install -y openjdk-8-jdk && \
    rm -rf /var/lib/apt/lists/*

RUN apt-get install -y opam
RUN apt-get update && apt-get install -y wget
RUN apt-get install autoconf zlib1g-dev -y
RUN apt-get install libgmp-dev pkg-config -y

RUN opam init --disable-sandboxing --reinit -a -y --compiler=4.08.0 && \
    eval $(opam env)

RUN opam install why3.1.7.2 --yes

RUN git clone https://github.com/jcrecio/jml2why3 jml2why3root
RUN cd jml2why3root/jml2why3

RUN opam init --yes
RUN opam switch 4.08.0
RUN eval $(opam env)

RUN opam install yojson --yes
RUN opam install re --yes
RUN opam install ppx_deriving --yes
RUN opam install alt-ergo --yes

CMD ["/bin/bash"]