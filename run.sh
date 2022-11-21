PATH2LIB=~/hw2/build/HW2/LLVMHW2.so        # Specify your build directory in the project
PASS=-fplicm-performance                   # Choose either -fplicm-correctness or -fplicm-performance

# Delete outputs from previous run.
rm -f default.profraw ${1}_prof ${1}_fplicm ${1}_no_fplicm *.bc ${1}.profdata *_output *.ll

# Convert source code to bitcode (IR)
clang -emit-llvm -c ${1}.c -o ${1}.bc
# Canonicalize natural loops
opt -enable-new-pm=0 -loop-simplify ${1}.bc -o ${1}.ls.bc
# Instrument profiler
opt -enable-new-pm=0 -pgo-instr-gen -instrprof ${1}.ls.bc -o ${1}.ls.prof.bc
# Generate binary executable with profiler embedded
clang -fprofile-instr-generate ${1}.ls.prof.bc -o ${1}_prof

# Generate profiled data
./${1}_prof > correct_output
llvm-profdata merge -o ${1}.profdata default.profraw

# Apply FPLICM
opt -enable-new-pm=0 -o ${1}.fplicm.bc -pgo-instr-use -pgo-test-profile-file=${1}.profdata -load ${PATH2LIB} ${PASS} < ${1}.ls.bc > /dev/null

# Generate binary excutable before FPLICM: Unoptimzied code
clang ${1}.ls.bc -o ${1}_no_fplicm
# Generate binary executable after FPLICM: Optimized code
clang ${1}.fplicm.bc -o ${1}_fplicm

# Produce output from binary to check correctness
./${1}_fplicm > fplicm_output

echo -e "\n=== Correctness Check ==="
if [ "$(diff correct_output fplicm_output)" != "" ]; then
    echo -e ">> FAIL\n"
else
    echo -e ">> PASS\n"
    # Measure performance
    echo -e "1. Performance of unoptimized code"
    time ./${1}_no_fplicm > /dev/null
    echo -e "\n\n"
    echo -e "2. Performance of optimized code"
    time ./${1}_fplicm > /dev/null
    echo -e "\n\n"
fi

# Cleanup
rm -f default.profraw ${1}_prof ${1}_fplicm ${1}_no_fplicm *.bc ${1}.profdata *_output *.ll
