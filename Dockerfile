FROM ubuntu
MAINTAINER Guillaume Claret

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y gcc make git

# Opam
RUN apt-get install -y opam
RUN opam init
ENV OPAMJOBS 6

# Coq
RUN opam install -y coq

# Dependencies
RUN v=1 opam repo add coq-stable https://github.com/coq/repo-stable.git
RUN opam install -y coq-function-ninjas coq-list-string

# Tools
RUN apt-get install -y inotify-tools

# Compile
ADD . /root/coq-moment
WORKDIR /root/coq-moment
CMD eval `opam config env`; ./configure.sh && while inotifywait *.v; do make; done