# namin/twelf

FROM ubuntu:12.10
MAINTAINER Nada Amin, namin@alum.mit.edu

# RUN apt-get install -y python-software-properties
RUN apt-get install -y software-properties-common

RUN add-apt-repository "deb http://archive.ubuntu.com/ubuntu $(lsb_release -sc) main universe restricted multiverse"

RUN apt-get update
RUN apt-get upgrade -y
RUN locale-gen en_US en_US.UTF-8

RUN apt-get install -y curl wget
RUN apt-get install -y git subversion
RUN apt-get install -y unzip
RUN apt-get install -y sed gawk

RUN mkdir /code

# NOTE(namin): I disabled some installations from source, because they get killed.

### ML ###
RUN apt-get install -y mlton-compiler

### Twelf ###
# --- killed ---
# RUN cd /code;\
#     git clone https://github.com/standardml/twelf.git;\
#     cd twelf;\
#     make mlton;\
#     make install
#
#### Install from binary ####
RUN  cd /code;\
     wget -nv http://twelf.plparty.org/releases/twelf-linux-1.7.1.tar.gz;\
     cp twelf/bin/twelf-server /usr/local/bin
