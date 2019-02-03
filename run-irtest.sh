if [ "$#" -ne 1 && "$#" -ne 0 ]; then
  echo "run-irtest.sh"
  echo "run-irtest.sh <random seed>"
  exit 1
fi

# of testing
n=5000
# clang path
clang=~/clang-7.0.1/bin/clang
# verbosity, replace n with y if want the script to be verbose
verbose=n
# random seed
if [ "$#" -eq 0 ]; then
  seed=0
else
  seed=$1
fi

rm -rf tmp/
mkdir tmp

echo "Generating & testing $n random programs.."
time lean --run ./src/irtest_run.lean $n $clang $verbose $seed
