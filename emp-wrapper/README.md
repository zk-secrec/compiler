# emp-wrapper
This subproject creates a C wrapper for the [emp-zk](https://github.com/emp-toolkit/emp-zk) library, which allows Rust bindings to be generated.

## Installation

First build the `emp-zk` tool using the instructions on their GitHub page. Building also needs libssl and libcrypto, but you should have them from building `emp-zk`. Then building for building the C wrapper, make sure that your working directory is `emp-wrapper` and run 

```
cmake -DCMAKE_INSTALL_PREFIX=<emp install location> .
make
```

If emp is installed system wide there should not be reason to specify the CMAKE_INSTALL_PREFIX.
