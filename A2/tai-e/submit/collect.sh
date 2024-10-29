TAIE_DIR=$(pwd)/src/main/java/pascal/taie &&
cp $TAIE_DIR/analysis/dataflow/analysis/constprop/ConstantPropagation.java ./submit &&
cp $TAIE_DIR/analysis/dataflow/solver/WorkListSolver.java ./submit &&
cp $TAIE_DIR/analysis/dataflow/solver/Solver.java ./submit &&
cd submit &&
zip ./A2.zip ./*.java &&
cd ..