# Building locally

This option is good if you wish to develop ZK-SecreC tools. Following steps
install the ZK-SecreC compiler and language server (but not Visual Studio Code
plugin).

First step is to install the stack build tool. On Debian based distributions one can write:

`$ sudo apt install haskell-stack`

On macOS a fast way to get started is also to install `haskell-stack` using Homebrew:

`$ brew install haskell-stack`

If this leads to trouble refer to the troubleshooting/installation guide at
https://docs.haskellstack.org/en/stable/install_and_upgrade/#macos

ZK-SecreC requires a relatively new version of Stack (> 2). If your distribution
has an older version of Stack you can upgrade it with:

`$ stack upgrade`

and then add `~/.local/bin` to your PATH.

You can now compile and install the ZK-SecreC compiler and language server with:

`$ stack install`

Stack will locally install the correct version of GHC for you before building.
If builds inexplicably start to fail during development it can, in some situations,
be fixed with:

`$ stack clean && stack install`

It's possible to build the compiler without installing using `stack build`.

Compiling ZK-SecreC further requires an installation of the Rust toolchain.
The recommended method of installing it is by using [Rustup](https://rustup.rs/).

# Using the compiler

The entrypoint to invoking the compiler is the script `runrust` in the 
repository root. The script generates the Rust source code, compiles it, and
executes the resulting binary which outputs the IR.

Usage instructions are provided by running the script without any arguments:

`$ ./runrust`

# ZK-SecreC vscode extension

The vscode extension adds syntax highlighting and language server integration.
Currently only syntax and typing errors are shown. Type information and
go-to-definition are work in progress.

See its [readme](vscode-zksc/README.md) for setup instructions.

# Building and using the "production" Docker image

The `Dockerfile` in the top-level directory builds a minimal docker image with
just the compiler.

Build the image:

`$ docker build -t zkscc .`

Save the image as .tar.gz file:

`$ docker save zkscc | gzip > zkscc.tar.gz`

The image can be re-created from the .tar.gz file using:

`$ docker load --input zkscc.tar.gz`

When running a container from the image you would probably want to access your
ZK-SecreC programs in the container. The simplest option for this is to use
[bind mounts](https://docs.docker.com/storage/bind-mounts/). Let's assume that
the local directory foo contains ZK-SecreC programs. Run a container using:

`$ docker run -it --rm -v "$(pwd)/foo":/zksc/workspace/foo zkscc /bin/bash`

The foo directory is now available in the working directory.

The image is bootstrapped with the Rust toolchain and the `runrust` script, so
the Rust compilation pipeline can also be run the same as locally.

The same container can be restarted if needed with `docker start <container ID>`
followed by `docker attach <container ID>`.

The Docker image can also be used non-interactively as a base image for other
application specific images (e.g. demonstrators).

# Using Visual Studio Code Docker dev container

This option is convenient if you wish to use the ZK-SecreC tools but not
necessarily develop them further. It gives you access to the ZK-SecreC compiler
and an IDE which you can use to develop proofs.

Install:

* [Visual Studio Code](https://code.visualstudio.com/),
* [Docker](https://docs.docker.com/get-docker/).

1. Open VS Code.
1. Open the Extensions panel using Ctrl + Shift + X or by clicking
   on the package icon in the left sidebar.
1. Search for "remote containers" and install the "Remote - Containers"
   extension.
1. Run `docker build -t zkscc .` in the repository root to build and tag the 
   dev container base image.

If you open the directory of this repository in VS Code it will now offer you
to open the directory in the dev container with ZK-SecreC tools.

After VS Code has opened the dev container it has installed the ZK-SecreC
extension as well. You can now work on .zksc files in the repository directory.

Open the panel (Ctrl + J or View -> Appearance -> Show Panel). Click on the
terminal tab. If no terminal is opened click the plus sign on the right of the
panel. You now have a shell running inside of the container and the repository
files are mounted in the container. To use the Rust compilation pipeline,
call the script included in the environment's path, e.g. `runrust`.

# Emp Backend

[Emp](https://github.com/emp-toolkit/emp-zk) is a ZK toolkit written in C++ which
allows a prover and verifier to perform arithmetic and boolean operations.
The "emp backend" replaces SIEVE IR generation with calls to the emp backend code
instead, allowing an interactive execution session of the .zksc code using the emp runtime.

The way this works is through a small wrapper named `emp-wrapper` which exposes
the necessary functionality. Then, Rust bindings are generated for that wrapper using
`bindgen` which is then called by the generated Rust code.

## Installation

To install the emp backend you need to compile the emp-wrapper library.
The build instructions for that are in the ./emp-wrapper readme.

## Usage

The emp backend can only be called through Rust via the `runrust` command.
Calling ./runrust will show details of the available flags (notably --emp).
You will need two run two instances of the program, one with `--emp --prover`
and the other with `--emp --verifier`. Building the two instances of the program
nearly at the same time can result in them not successfully connecting.

If running emp over the network, use the `--emp-addr` flag to specify address and port.

## Quirks

emp-toolkit has two kinds of integers: bit vectors and fixed-precision integers.
The current emp backend as of 2022-08-15 only has bindings for the fixed-precision kind,
which operates in the Mersenne61 modulus.
For larger numbers you can use the BigInt.zksc module from the standard library.

Booleans are also encoded as M61 integers, and logical operations are done through
arithmetic ones. This means that in efficiency they are ranked as: and >> or >>>> xor.
