TAIE_DIR=$(pwd)/src/main/java/pascal/taie &&
cp $TAIE_DIR/analysis/dataflow/analysis/LiveVariableAnalysis.java ./submit &&
cp $TAIE_DIR/analysis/dataflow/solver/IterativeSolver.java ./submit &&
cp $TAIE_DIR/analysis/dataflow/solver/Solver.java ./submit &&
cd submit &&
zip ./A1.zip ./*.java &&
cd ..