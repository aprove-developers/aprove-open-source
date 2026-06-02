FROM ubuntu:24.04
USER root

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y software-properties-common

RUN apt-get update && apt-get install -y \
  openjdk-25-jdk \
  git \
  minisat2 \
  unzip \
  mono-runtime \
  xsltproc \
  libxml2-utils

RUN apt install z3

RUN apt update && apt install -y \
  libgmp10

WORKDIR /opt

COPY /bundle /opt/bundle

WORKDIR /opt/bundle/cpfconverter

ENV PATH="/opt/bundle/cpfconverter:/opt/bundle/irankfinder/1.3.1/irankfinder/partialevaluation/bin:/opt/bundle/irankfinder/1.3.1/irankfinder/ppl:/opt/bundle/irankfinder/1.3.1/irankfinder:/opt/bundle/bin:/usr/bin:${PATH}"
ENV LD_LIBRARY_PATH="/opt/bundle/c_lib"
ENV C_INCLUDE_PATH="/opt/bundle/fake_include"
ENV LOAT_PATH="/opt/bundle/bin"
ENV KOAT2_PATH="/opt/bundle/bin"
ENV T2_PATH="/opt/bundle/t2"
ENV APROVE="/opt/bundle/aprove.jar"
ENV JAVA_HOME="/usr/lib/jvm/java-25-openjdk-amd64"
ENV PATH="${JAVA_HOME}/bin:${PATH}"

#Make all bin files executable
RUN chmod +x /opt/bundle/bin
RUN chmod +x /opt/bundle/cpfconverter
RUN chmod +x /opt/bundle/bin/loat

#Copy License
WORKDIR /licenses
COPY LICENSE aprove

#Copy Examples
# COPY /examples /examples

WORKDIR /input

COPY lib /usr/bin/lib
COPY solver             /usr/bin/solver
COPY handlers/ /usr/bin/handlers/
RUN chmod +x /usr/bin/solver

# help the dispatcher if it honors SOLVER_ROOT
ENV SOLVER_ROOT="/usr/bin"

ENTRYPOINT ["solver"]
