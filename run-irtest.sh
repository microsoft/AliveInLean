# of testing
n=10000
# clang path
clang=~/clang-7.0.1/bin/clang
# verbosity, replace n with y if want the script to be verbose
verbose=n

rm -rf tmp/
mkdir tmp

echo "Generating & testing $n random programs.."
time lean --run ./src/irtest_run.lean $n $clang $verbose
