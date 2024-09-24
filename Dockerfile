FROM debian:buster-slim as emp-builder
RUN apt-get update && apt-get install -y zlib1g python3 wget sudo git cmake build-essential clang
COPY emp-wrapper /emp-wrapper/
WORKDIR /emp-wrapper
RUN wget https://raw.githubusercontent.com/emp-toolkit/emp-readme/master/scripts/install.py && \
    sed -i 's|X|XX|g' install.py && \
    sed -i 's|cmake \.|cmake -DCMAKE_INSTALL_PREFIX=/emp-wrapper \.|' install.py && \
    python3 install.py --deps --tool --ot --zk
RUN cmake -DCMAKE_INSTALL_PREFIX=/emp-wrapper . && make

#---
FROM haskell:8.10.7-buster AS zkscc-builder
WORKDIR /zksc
COPY Setup.hs stack.yaml stack.yaml.lock zkscc.cabal ./
COPY sieveir/stack.yaml sieveir/sieveir.cabal /zksc/sieveir/
RUN stack build --system-ghc --dependencies-only
COPY compiler compiler/
COPY language-server language-server/
COPY sieveir sieveir/
COPY src src/
COPY test test/
COPY stdlib stdlib/
COPY circuits circuits/
RUN stack build --system-ghc --ghc-options=-O2 zkscc && \
    stack install
#---

FROM rust:slim-buster AS zkscc
RUN apt-get update && apt-get install -y zlib1g python3 wget sudo git cmake build-essential clang curl
WORKDIR /zksc/workspace
COPY --from=zkscc-builder /root/.local/bin/zkscc /usr/bin/zkscc
COPY --from=zkscc-builder /root/.local/bin/zksc-language-server /usr/bin/zkscc-language-server
COPY --from=emp-builder /emp-wrapper emp-wrapper/
COPY circuits/ /usr/lib/zksc/circuits/
COPY src/Rust src/Rust/
COPY runrust .
RUN sed -i 's/stack exec zkscc --/zkscc/' runrust

# ENTRYPOINT / CMD purposely omitted
