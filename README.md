# tnn-miner
# An open-source Astrobwtv3 miner

**Dependencies are as follows:**
  - OpenSSL v3.0.2 (static libs)
  - Boost v1.8.2 (b2 with link=static)
  - UDNS (UNIX only. sudo apt-get install libudns-dev)
  - FMT (header only)

## This repo can be built from source via cmake once these libraries are installed on your system
```
git clone https://github.com/Tritonn204/tnn-miner.git
cd tnn-miner
mkdir build
cd build
cmake ..
make
```
### MinGW will work, just swap "make" with "mingw32-make".

Do note that CMakeLists.txt will need to be altered if your libraries are installed at neither **C:/mingw64** nor the **root dir** of this project on Windows.

# USAGE
This miner can be activated from the command line with the following parameters. Simply adjust the syntax for use with your shell or terminal of choice!
```
OPTIONS
    -gpu:
        Mine with GPU instead of CPU
    -daemon-address, -d: 
        Dero node/pool URL or IP address to mine to
    -port, -p: 
        The port used to connect to the Dero node
    -wallet, -w: 
        Wallet address for receiving mining rewards
    -threads, -t: (optional) 
        The amount of mining threads to create, default is 1
    -dev-fee, -f: (optional) 
        Your desired dev fee percentage, default is 2.5, minimum is 1
    -no-lock: (optional) 
        Disables CPU affinity / CPU core binding (must be final arg if running benchmark)
    -help, -h: (must be first arg)
        Shows help
    -batch-size, -b: (GPU Setting)
        Sets batch size used for GPU mining
    -sabench: (must be first arg)
        Runs a benchmark for divsufsort on snapshot files in the 'tests' directory (must supply your own input files for now)
DEBUG
    -test: (must be first arg)
        Runs a set of tests to verify AstrobwtV3 is working (1 test expected to fail)
        Params: (optional)
          -o <num> : Sets which branch op to benchmark (0-255), benchmark will be skipped if unspecified
          -l <num> : Sets length of the processed chunk in said benchmark (default 15) 
    -benchmark <A> <B>:
        Runs a mining benchmark with <A> threads for <B> seconds for hashrate testing
        You may insert the -no-lock flag after <A> and <B> if desired. 
```
### If the miner is run without any args, a CLI wizard will simply ask you to provide the required options one at a time.

If you intend to build from source without dev fees, please consider a one-time donation to the Dero address **_tritonn_** (Dero Name Service). 

Dev fees allow me to invest more time into maintaining, updating, and improving tnn-miner.
